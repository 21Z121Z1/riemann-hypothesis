import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrderPreservingPowerHomAlgClosurePrimeFiel
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.PowAut

theorem exists_coprime_lift (N k a : ℕ) (hN : 0 < N) (hk : 0 < k) (ha : a.Coprime N) :
    ∃ b : ℕ, b.Coprime (N * k) ∧ b ≡ a [MOD N] := by
  haveI : NeZero (N * k) := ⟨(Nat.mul_pos hN hk).ne'⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Dvd.intro k rfl : N ∣ N * k)
    (ZMod.unitOfCoprime a ha)
  refine ⟨(u : ZMod (N * k)).val, ZMod.val_coe_unit_coprime u, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have h := congrArg (fun v : (ZMod N)ˣ => (v : ZMod N)) hu
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
    ZMod.coe_unitOfCoprime] at h
  rw [← h, ZMod.natCast_val]

theorem exists_exponents (M n : ℕ) (hM : 0 < M) (hn : n.Coprime M) :
    ∃ a : ℕ → ℕ, a 0 = n ∧ (∀ j, (a j).Coprime (M * j.factorial)) ∧
      ∀ i j, i ≤ j → a j ≡ a i [MOD M * i.factorial] := by
  have step : ∀ j : ℕ, ∀ a : {a : ℕ // a.Coprime (M * j.factorial)},
      ∃ b : {b : ℕ // b.Coprime (M * (j + 1).factorial)}, b.1 ≡ a.1 [MOD M * j.factorial] := by
    intro j a
    obtain ⟨b, hb, hb'⟩ := exists_coprime_lift (M * j.factorial) (j + 1) a.1
      (Nat.mul_pos hM j.factorial_pos) j.succ_pos a.2
    refine ⟨⟨b, ?_⟩, hb'⟩
    rw [Nat.factorial_succ, mul_comm (j + 1), ← mul_assoc]
    exact hb
  choose f hf using step
  let s : ∀ j : ℕ, {a : ℕ // a.Coprime (M * j.factorial)} := fun j =>
    Nat.rec (motive := fun j => {a : ℕ // a.Coprime (M * j.factorial)})
      ⟨n, by simpa using hn⟩ f j
  have hs : ∀ j, s (j + 1) = f j (s j) := fun j => rfl
  refine ⟨fun j => (s j).1, rfl, fun j => (s j).2, ?_⟩
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact Nat.ModEq.refl _
  | succ j hij ih =>
    have h1 : (s (j + 1)).1 ≡ (s j).1 [MOD M * j.factorial] := by rw [hs]; exact hf j (s j)
    exact (h1.of_dvd (Nat.mul_dvd_mul_left M (Nat.factorial_dvd_factorial hij))).trans ih

theorem orderOf_pos_of_ne_zero (g : ℕ) [Fact g.Prime] (x : AlgebraicClosure (ZMod g))
    (hx : x ≠ 0) : 0 < orderOf x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  haveI := Fintype.ofFinite (IntermediateField.adjoin (ZMod g) {x})
  let y : IntermediateField.adjoin (ZMod g) {x} :=
    ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  have h2 : x ^ (Fintype.card (IntermediateField.adjoin (ZMod g) {x}) - 1) = 1 :=
    congrArg Subtype.val h1
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨_, Nat.sub_pos_of_lt Fintype.one_lt_card, h2⟩)

theorem exists_powHom {K : Type*} [Field K] (hK : ∀ x : K, x ≠ 0 → 0 < orderOf x)
    (M n : ℕ) (hM : 0 < M) (hn : n.Coprime M) :
    ∃ θ : K →* K, Function.Injective θ ∧ (∀ x, orderOf (θ x) = orderOf x) ∧
      ∀ x, x ^ M = 1 → θ x = x ^ n := by
  classical
  obtain ⟨a, ha0, hac, ha⟩ := exists_exponents M n hM hn
  let t : K → K := fun x => if x = 0 then 0 else x ^ a (orderOf x)
  have t0 : t 0 = 0 := if_pos rfl
  have ht : ∀ x : K, x ≠ 0 → ∀ j, orderOf x ≤ j → t x = x ^ a j := by
    intro x hx j hj
    have : t x = x ^ a (orderOf x) := if_neg hx
    rw [this]
    have h := (ha _ _ hj).of_dvd
      (Dvd.dvd.mul_left (Nat.dvd_factorial (hK x hx) le_rfl) M)
    rw [← pow_mod_orderOf x (a j), ← pow_mod_orderOf x (a (orderOf x)), h]
  let θ : K →* K :=
    { toFun := t
      map_one' := by rw [ht 1 one_ne_zero _ le_rfl, one_pow]
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · rw [hx, zero_mul, t0, zero_mul]
        by_cases hy : y = 0
        · rw [hy, mul_zero, t0, mul_zero]
        rw [ht x hx (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          ht y hy (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          ht _ (mul_ne_zero hx hy) (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          mul_pow] }
  have hθ : ∀ x, θ x = t x := fun _ => rfl
  have hord : ∀ x, orderOf (θ x) = orderOf x := by
    intro x
    by_cases hx : x = 0
    · rw [hθ, hx, t0]
    rw [hθ, ht x hx _ le_rfl]
    exact Nat.Coprime.orderOf_pow ((hac (orderOf x)).coprime_dvd_right
      (Dvd.dvd.mul_left (Nat.dvd_factorial (hK x hx) le_rfl) M)).symm
  have hne : ∀ x : K, x ≠ 0 → θ x ≠ 0 := by
    intro x hx
    rw [hθ, ht x hx _ le_rfl]
    exact pow_ne_zero _ hx
  refine ⟨θ, ?_, hord, ?_⟩
  · intro x y hxy
    by_cases hy : y = 0
    · by_contra h
      exact hne x (hy ▸ h) (by rw [hxy, hy, hθ, t0])
    have h1 : θ (x * y⁻¹) * θ y = 1 * θ y := by
      rw [← map_mul, inv_mul_cancel_right₀ hy, one_mul, hxy]
    have h2 := mul_right_cancel₀ (hne y hy) h1
    have h3 : orderOf (x * y⁻¹) = 1 := by rw [← hord, h2, orderOf_one]
    rw [orderOf_eq_one_iff, mul_inv_eq_one₀ hy] at h3
    exact h3
  · intro x hxM
    have hx : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne'] at hxM
      exact zero_ne_one hxM
    have h := (ha 0 (orderOf x) (Nat.zero_le _)).of_dvd
      (Dvd.dvd.mul_right (orderOf_dvd_of_pow_eq_one hxM) _)
    rw [hθ, ht x hx _ le_rfl, ← ha0, ← pow_mod_orderOf x (a 0),
      ← pow_mod_orderOf x (a (orderOf x)), h]

theorem exists_powHom_fbar : ∀ (g : ℕ) [Fact g.Prime] (M n : ℕ), 0 < M → n.Coprime M →
    ∃ θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g, Function.Injective θ ∧
      (∀ x, orderOf (θ x) = orderOf x) ∧ ∀ x, x ^ M = 1 → θ x = x ^ n :=
  fun g _ M n hM hn => exists_powHom (orderOf_pos_of_ne_zero g) M n hM hn

end GlobalTheory.PowAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeEqMulPrimitiveRootSubOnePowStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_eq_mul_primitiveRoot_sub_one_pow' : ∀ (l : ℕ) [Fact l.Prime] (H : ℕ) (ζ : PadicComplex l), IsPrimitiveRoot ζ (l ^ (1 + n0 l H)) → ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  first | exact @GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow | exact GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow | (intros; apply GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesLimitLatStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_series_limit_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (M : ℕ) (c : ℕ → P.R.BdR), (∀ k, c k ∈ FilB P 0) → (∀ n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, c k ∈ Lat AI M n) → ∃ b ∈ FilB P 0, ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, b - ∑ k ∈ Finset.range R, c k ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.exists_series_limit_Lat | exact GlobalTheory.ExpImage.exists_series_limit_Lat | (intros; apply GlobalTheory.ExpImage.exists_series_limit_Lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableLatticeCompactGroupStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_lattice_compact_group : ∀ {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp LL O : Type} [Field Qp] [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O), Nonempty (Lattice (O := O) A.ρ) := by
  first | exact @GlobalTheory.StableLat.exists_lattice | exact GlobalTheory.StableLat.exists_lattice | (intros; apply GlobalTheory.StableLat.exists_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnityStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_padicInt_mul_rootsOfUnity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (ω : Fin n → Om l), (∀ i, ω i ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ω i ^ m = 1) ∧ c = ∑ i, algebraMap ℚ_[l] (Om l) (z i : ℚ_[l]) * ω i := by
  first | exact @GlobalTheory.UnramSpan.exists_sum_rootsOfUnity | exact GlobalTheory.UnramSpan.exists_sum_rootsOfUnity | (intros; apply GlobalTheory.UnramSpan.exists_sum_rootsOfUnity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSymbolBasis
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbolBasis

open GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : ThetaL P AI)

theorem theta_zero : J.θ 0 = 0 := by
  have h := J.θ_add 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero] at h
  simpa using h

theorem theta_sum {ι : Type} (s : Finset ι) (f : ι → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) : J.θ (∑ i ∈ s, f i) = ∑ i ∈ s, J.θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero J
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      J.θ_add _ (hf a) _ (Submodule.sum_mem _ fun i _ => hf i), ih]

theorem om_mul_mem (c : Om l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    algebraMap (Om l) P.R.BdR c * x ∈ (P.PD (botExt l)).Fil 0 := by
  simpa using (P.PD (botExt l)).Fil_mul _ _ _ _ (om_mem c) hx

theorem theta_comb {n : ℕ} (c : Fin n → Om l) (f : Fin n → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) :
    J.θ (∑ i, algebraMap (Om l) P.R.BdR (c i) * f i) = ∑ i, (c i : PadicComplex l) * J.θ (f i) := by
  rw [theta_sum J _ _ fun i => om_mul_mem (c i) (hf i)]
  exact Finset.sum_congr rfl fun i _ => by rw [J.θ_mul _ (om_mem _) _ (hf i), J.θ_Om]

omit J in
theorem shift_act (a : ℤ) (g : GQ l) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) *
        P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
  rw [map_mul, DeRhamSymbol.act_zpow, ← mul_assoc, ← mul_assoc,
    ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
    map_one, one_mul]

omit J in
theorem exists_adapted {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V)
    (hL : FiniteDimensional Qp LL) (hV : FiniteDimensional LL V) (hDR : IsDR PD ρ) :
    ∃ (x : Fin d → Fin d → BdR) (u : Fin d → ℤ), (∀ k, (∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x k i)) = x k) ∧
      ∀ i, x k i ∈ PD.Fil (u k)) ∧ ∀ (a : ℤ) (c : Fin d → K), (∀ k, u k ≠ a → c k = 0) →
      (∀ i, ∑ k, algebraMap K BdR (c k) * x k i ∈ PD.Fil (a + 1)) → ∀ k, c k = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  haveI : Nontrivial V := ⟨⟨b ⟨0, hd⟩, 0, b.ne_zero _⟩⟩
  haveI := PD.finK
  have hfin : Module.Finite LL ↥(DdR PD ρ) := by
    apply Module.finite_of_finrank_pos
    rw [hDR]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  obtain ⟨Φ, -, hΦ⟩ := GlobalTheory.exists_coord_tensor_dR PD ρ b
  obtain ⟨D, hD, hDf, hDr⟩ := GlobalTheory.deRham_invariants_coord_finrank PD ρ b hL hfin hDR Φ hΦ
  obtain ⟨x, u, hx, hind⟩ := GlobalTheory.exists_family_adapted_filtration K (Fin d → BdR) D
    (fun a => Submodule.pi Set.univ fun _ => PD.Fil a) d hDf hDr
    (fun a z hz i hi => PD.Fil_anti a (hz i hi))
    (fun z => by
      have anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
      choose f hf using fun i => PD.Fil_exh (z i)
      obtain ⟨m, hm⟩ := (Set.finite_range f).bddBelow
      exact ⟨m, fun i _ => anti (hm ⟨i, rfl⟩) (hf i)⟩)
    (fun z hz => funext fun i => PD.Fil_sep _ fun a => hz a i trivial)
  refine ⟨x, u, fun k => ⟨(hD _).1 (hx k).1, fun i => (hx k).2 i trivial⟩, fun a c hc hs => ?_⟩
  refine hind a c hc fun i _ => ?_
  have := hs i
  simp only [← Algebra.smul_def] at this
  simpa only [Finset.sum_apply, Pi.smul_apply, SetLike.mem_coe] using this

omit J in
theorem sum_mem_DdR {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V) (x : Fin d → BdR)
    (hx : ∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x i)) = x) :
    ∑ i, b i ⊗ₜ[Qp] x i ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  intro g
  have hact : ∀ (v : V) (y : BdR),
      actVdR PD ρ g (v ⊗ₜ y) = ρ g v ⊗ₜ PD.actdR g y := by
    intro v y
    unfold actVdR
    rw [TensorProduct.AlgebraTensorModule.map_tmul]
    rfl
  obtain ⟨Φ, h, -⟩ := GlobalTheory.exists_tensor_coord_of_basis (M := BdR) b
  apply Φ.injective
  funext i
  rw [map_sum, map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  simp only [hact, h, Module.Basis.repr_self]
  have h1 := congrFun (hx g) i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ← Algebra.smul_def] at h1
  rw [h1, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Finsupp.single_apply, hij]
  · simp

omit J in

theorem exists_symbol_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (θ : ThetaL P AI) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsDR (P.PD K) T.ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)), (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) → ∀ t : (P.R.BdR)ˣ, (t : P.R.BdR) = P.ιB P.tB → ∃ (u : Fin d → ℤ) (y : Fin d → Fin d → P.R.BdR), (∀ k i, y k i ∈ (P.PD K).Fil 0) ∧ (∀ k, ∑ i, b i ⊗ₜ[ℚ_[l]] (y k i * ((t ^ u k : (P.R.BdR)ˣ) : P.R.BdR)) ∈ DdR (P.PD K) T.ρ) ∧ LinearIndependent (PadicComplex l) (fun k i => θ.θ (y k i)) ∧ ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ (fun i => θ.θ (y k i)) = fun i => θ.θ (y k i) := by
  intro l _ P AI J K LL T hDR d b M hM t ht
  obtain rfl : t = tU P := Units.ext ht
  obtain ⟨x, u, hx, hind⟩ := exists_adapted (P.PD K) T.ρ b LL.2 T.fdim hDR
  have key : ∀ k i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i ∈ (P.PD (botExt l)).Fil 0 :=
    fun k i => (shift_iff J (u k) 0 _).2 (by
      rw [add_zero]; exact (mem_iff K _ _).1 ((hx k).2 i))
  have heq : ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ
      (fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i)) =
      fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i) := by
    intro σ hσ k
    funext i
    generalize hN : (fun i j => b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i : Fin d → Fin d → ℚ_[l]) = N
    have hN' : ∀ i j, b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i = N i j := fun i j => congrFun (congrFun hN i) j
    have h1 := congrFun ((hx k).1 ⟨σ, hσ⟩) i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, P.PD_actdR, hN'] at h1
    have h2 : ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i =
        ∑ j, algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l)
          (((P.χQ σ ^ u k : ℚ_[l]ˣ) : ℚ_[l]) * N i j)) *
          P.actQdR σ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k j) := by
      conv_lhs => rw [← h1]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, shift_act, ← IsScalarTower.algebraMap_apply,
        map_mul (algebraMap ℚ_[l] P.R.BdR), mul_left_comm, mul_assoc]
    conv_rhs => rw [h2, theta_comb J _ _ fun j => act_mem σ (key k j)]
    simp only [twAct, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [J.θ_act σ _ (key k j), hM ⟨σ, hσ⟩ i j, hN', ← mul_assoc, chiC, ← map_mul]
    rfl
  refine ⟨u, fun k i => ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i,
    fun k i => (mem_iff K _ _).2 (key k i), fun k => ?_, ?_, heq⟩
  · have : ∀ i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i *
        ((tU P ^ u k : P.R.BdRˣ) : P.R.BdR) = x k i := fun i => by
      rw [mul_right_comm, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
        one_mul]
    simp only [this]
    exact sum_mem_DdR (P.PD K) T.ρ b _ (hx k).1
  · refine GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise l AI.actC P.χQ (GK K) K.1
      (tate_invariants_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K) d d M _ u heq ?_
    intro a c hc hs
    refine hind a c hc fun i => ?_
    have h1 := congrFun hs i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [← theta_comb J (fun k => ((c k : ↥K.1) : Om l)) _ (fun k => key k i),
      J.θ_ker _ (Submodule.sum_mem _ fun k _ => om_mul_mem _ (key k i))] at h1
    rw [mem_iff K, ← shift_iff J, Finset.mul_sum]
    convert h1 using 2 with k
    by_cases hk : u k = a
    · rw [hk, mul_left_comm]
      rfl
    · simp [hc k hk]

end GlobalTheory.DeRhamSymbolBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceFormIntegralIffGoodCoeff
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

theorem exists_trace_form_integral_iff : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ lam : LL →ₗ[ℚ_[l]] ℚ_[l], ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a := by
  intro l _ LL _ _ _ O _ _ hG
  have hint := (good_coeff_integers l LL O hG).1
  obtain ⟨⟨hD, hDVR, hFr⟩, hfin, hmod, htop, hopen⟩ := hG
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI : FiniteDimensional ℚ_[l] LL := hfin
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let A : Subring LL := (algebraMap O LL).range
  have hZ : ∀ u : ℤ_[l], algebraMap ℤ_[l] LL u ∈ A := fun u =>
    padicInt_mem A (by rw [RingHom.coe_range]; exact hopen) u
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  let ψ : O ≃+* A := RingEquiv.ofBijective (algebraMap O LL).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap O LL).rangeRestrict_surjective⟩
  have hψ : ∀ a : A, algebraMap O LL (ψ.symm a) = a := fun a =>
    congrArg Subtype.val (ψ.apply_symm_apply a)
  let f : ℤ_[l] →+* O := ψ.symm.toRingHom.comp ((algebraMap ℤ_[l] LL).codRestrict A hZ)
  letI : Algebra ℤ_[l] O := f.toAlgebra
  haveI : IsScalarTower ℤ_[l] O LL := IsScalarTower.of_algebraMap_eq
    (fun u => (hψ ((algebraMap ℤ_[l] LL).codRestrict A hZ u)).symm)
  haveI : IsIntegralClosure O ℤ_[l] LL :=
    { algebraMap_injective := hinj
      isIntegral_iff := fun {x} => by
        rw [← Set.mem_range]
        exact (hint x).symm }
  let D : FractionalIdeal (nonZeroDivisors O) LL := FractionalIdeal.dual ℤ_[l] ℚ_[l] 1
  have hD0 : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ_[l] ℚ_[l] one_ne_zero
  haveI hP : (D : Submodule O LL).IsPrincipal := FractionalIdeal.isPrincipal D
  set c : LL := Submodule.IsPrincipal.generator (D : Submodule O LL) with hc
  have hDc : (D : Submodule O LL) = Submodule.span O {c} :=
    (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hc0 : c ≠ 0 := by
    intro h
    apply hD0
    apply FractionalIdeal.coeToSubmodule_injective
    show (D : Submodule O LL) = ((0 : FractionalIdeal (nonZeroDivisors O) LL) : Submodule O LL)
    rw [hDc, h, FractionalIdeal.coe_zero]
    exact Submodule.span_singleton_eq_bot.2 rfl
  refine ⟨(Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c), fun a => ?_⟩
  have key : (∀ b : O, ∃ u : ℤ_[l], (Algebra.trace ℚ_[l] LL) (c * (a * algebraMap O LL b)) = (u : ℚ_[l]))
      ↔ c * a ∈ D := by
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors O) LL) ≠ 0)]
    constructor
    · intro h y hy
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      obtain ⟨u, hu⟩ := h b
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc, hu]
      rfl
    · intro h b
      obtain ⟨u, hu⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc] at hu
      rw [← hu]
      rfl
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [key, ← FractionalIdeal.mem_coe, hDc, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, mul_comm] at hz
    exact mul_left_cancel₀ hc0 hz
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]⟩

end GlobalTheory.GoodCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weak_topology_witt_tilt_tensor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ Continuous (fun p : ↥(GK K) × TW (RW LL) T => TWact (AI.gRW LL (p.1 : GQ l)) T p.1 p.2) ∧ Topology.IsEmbedding (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ CompactSpace ↥T.L.T ∧ ∀ U ∈ nhds (0 : ↥T.L.T), ∃ k : ℕ, ∀ t : ↥T.L.T, l ^ k • t ∈ U := by
  first | exact @GlobalTheory.WeakTop.exists_weakTop | exact GlobalTheory.WeakTop.exists_weakTop | (intros; apply GlobalTheory.WeakTop.exists_weakTop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocyclesStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  first | exact @GlobalTheory.Cut.Coc.main | exact GlobalTheory.Cut.Coc.main | (intros; apply GlobalTheory.Cut.Coc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKsEq
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem finrank_Ks_eq : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (s : ℕ), 0 < s → finrank ℚ_[l] ↥(Loc.Ks K s) = finrank ℚ_[l] ↥(Loc.K0 K) * (l ^ (s - 1) * (l - 1)) := by
  intro l _ K s hs
  rw [GlobalTheory.Cyc.finrank_Ks K s hs, mul_comm (l - 1)]

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory

theorem finrank_le_of_subset_closure_range {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (J : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hdense : (K : Set (PadicAlgCl l)) ⊆ closure (Set.range J)) :
    finrank ℚ_[l] ↥K ≤ finrank ℚ E := by
  classical
  let b := Module.finBasis ℚ E
  let S : Submodule ℚ_[l] (PadicAlgCl l) := Submodule.span ℚ_[l] (Set.range fun k => J (b k))
  have hfd : FiniteDimensional ℚ_[l] S := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hcl : IsClosed (S : Set (PadicAlgCl l)) := Submodule.closed_of_finiteDimensional S
  have hsub : Set.range J ⊆ S := by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine S.sum_mem fun k _ => ?_
    have e : J (b.repr x k • b k) = ((b.repr x k : ℚ) : ℚ_[l]) • J (b k) := by
      rw [Rat.smul_def, map_mul, map_ratCast, Algebra.smul_def, map_ratCast]
    rw [e]
    exact S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  have hle : K.toSubalgebra.toSubmodule ≤ S := fun x hx => closure_minimal hsub hcl (hdense hx)
  have h1 : finrank ℚ_[l] ↥K.toSubalgebra.toSubmodule ≤ finrank ℚ_[l] S := Submodule.finrank_mono hle
  have h2 : finrank ℚ_[l] S ≤ finrank ℚ E := by
    have := finrank_range_le_card (R := ℚ_[l]) (fun k => J (b k))
    simpa [Set.finrank] using this
  exact le_trans h1 h2

theorem bridge_finrank_le (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 ≤ 4 * D.R.n := by
  have h1 : finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h2 := finrank_le_of_subset_closure_range
    ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw.1 (D.nbr i w hw).j_dense
  have h3 : D.R.n = D.R.ord := rfl
  have h4 : finrank ℚ D.host.E = 4 * D.R.n := by rw [h1, h3]
  exact le_trans h2 h4.le

end GlobalTheory
end

