import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0201
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0142
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0147
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0208
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import GroundTheory.PAdicHodge.TiltField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
section
namespace GlobalTheory

open Polynomial IsDiscreteValuationRing

theorem associated_primitiveRoot_sub_one_pow_totient_prime_pow {O : Type} [CommRing O] [IsDomain O]
    {l k : ℕ} (hl : l.Prime) {ζ : O} (hζ : IsPrimitiveRoot ζ (l ^ (k + 1))) :
    Associated ((ζ - 1) ^ Nat.totient (l ^ (k + 1))) (l : O) := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h1 := Polynomial.eval_one_cyclotomic_prime_pow (R := O) (p := l) k
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
  rw [← h1, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun μ hμ => ?_
  have hμ' : IsPrimitiveRoot μ (l ^ (k + 1)) :=
    (mem_primitiveRoots (pow_pos hl.pos _)).1 hμ
  obtain ⟨i, -, hi, rfl⟩ := (hζ.isPrimitiveRoot_iff).1 hμ'
  simpa using (hζ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right

theorem nval_primitiveRoot_prime_pow_sub_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l k : ℕ), l.Prime → 1 ≤ k → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ ζ : O, IsPrimitiveRoot ζ (l ^ k) → ζ - 1 ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (ζ - 1) = 1 / (Nat.totient (l ^ k) : ℝ) := by
  intro O _ _ _ l k hl hk hl0 hlu ζ hζ
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hass := associated_primitiveRoot_sub_one_pow_totient_prime_pow hl hζ
  have hφ : 0 < Nat.totient (l ^ (k + 1)) := Nat.totient_pos.2 (pow_pos hl.pos _)
  have hne : ζ - 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hφ.ne'] at hass
    exact hl0 ((associated_zero_iff_eq_zero _).1 hass.symm)
  refine ⟨hne, ?_⟩
  have hv : addVal O ((ζ - 1) ^ Nat.totient (l ^ (k + 1))) = addVal O (l : O) :=
    (addVal_eq_iff_associated _ _).2 hass
  rw [addVal_pow] at hv
  have ht : addVal O (ζ - 1) ≠ ⊤ := fun h => hne (addVal_eq_top_iff.1 h)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 ht
  have hl1 : addVal O (l : O) ≠ 0 := fun h => hlu (addVal_eq_zero_iff.1 h)
  have hv' : addVal O (l : O) = ((Nat.totient (l ^ (k + 1)) * a : ℕ) : ℕ∞) := by
    rw [← hv, ← ha]; simp
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hl1
    rw [hv']; simp
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [hv', ← ha, ENat.toNat_coe, ENat.toNat_coe]
  have : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
  have : (Nat.totient (l ^ (k + 1)) : ℝ) ≠ 0 := by exact_mod_cast hφ.ne'
  push_cast
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemHfDOfRestriction
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory

open TensorProduct

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V)

theorem corHf_actVB_tmul (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := by
  simp [actVB]

noncomputable def corHfRepVB : Representation LL G (V ⊗[Qp] B) where
  toFun g := actVB PD ρ g
  map_one' := by
    ext v b
    simp [corHf_actVB_tmul]
  map_mul' g h := by
    ext v b
    simp [corHf_actVB_tmul]

def corHfRepO (O : Type) [CommRing O] [Algebra O LL] [Module O V] [IsScalarTower O LL V] :
    Representation O G V where
  toFun g := (ρ g).restrictScalars O
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul LL V]

theorem index_smul_mem_HfD [CharZero LL] (L : Lattice (O := O) ρ) (hρ : ∀ g, Continuous (ρ g))
    (hρ' : ∀ x, Continuous fun g => ρ g x) (H : Subgroup G) [H.Normal] [H.FiniteIndex]
    (hH : IsOpen (H : Set G)) (Z f₀ : G → V) (hZ : ContinuousOn Z H)
    (hc : ∀ g ∈ H, ∀ h ∈ H, Z (g * h) = Z g + ρ g (Z h))
    (hX : ∃ X : V ⊗[Qp] B, ∀ h ∈ H, Z h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h X - X)
    (h₀ : ∀ g h, f₀ (g * h) - (f₀ g + ρ g (f₀ h)) ∈ L.T) (hZf : ∀ h ∈ H, Z h - f₀ h ∈ L.T) :
    (fun g => H.index • (Submodule.Quotient.mk (f₀ g) : V ⧸ L.T)) ∈ HfD PD L := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨F, hF, hFc, ⟨x, hx⟩, hY⟩ := exists_corestriction_cocycle O G V (corHfRepO ρ O) H hH hρ hρ'
    Z hZ hc
  obtain ⟨x', hx'⟩ := hY L.T L.stable f₀ 0 h₀ (by simpa using hZf)
  obtain ⟨X, hX⟩ := hX
  have hmul : ∀ a b y, actVB PD ρ a (actVB PD ρ b y) = actVB PD ρ (a * b) y := by
    intro a b y
    exact (LinearMap.congr_fun ((corHfRepVB PD ρ).map_mul a b) y).symm
  have h1 : ∀ g (v : V), actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
    intro g v
    rw [corHf_actVB_tmul, map_one]
  obtain ⟨y, hy⟩ := index_smul_cocycle_eq_coboundary LL G (V ⊗[Qp] B) (corHfRepVB PD ρ) H
    (fun g => F g ⊗ₜ[Qp] (1 : B))
    (by
      intro g h
      change _ = _ + actVB PD ρ g _
      rw [h1, hFc, add_tmul]
      rfl)
    ⟨(∑ q : G ⧸ H, actVB PD ρ q.out X) + x ⊗ₜ[Qp] (1 : B), by
      intro h hh
      change _ = actVB PD ρ h _ - _
      rw [hx h hh, finsum_eq_sum_of_fintype, add_tmul, sum_tmul, map_add, map_sum, h1, sub_tmul]
      have : ∀ q : G ⧸ H, (corHfRepO ρ O q.out (Z (q.out⁻¹ * h * q.out))) ⊗ₜ[Qp] (1 : B) =
          actVB PD ρ h (actVB PD ρ q.out X) - actVB PD ρ q.out X := by
        intro q
        change (ρ q.out _) ⊗ₜ[Qp] (1 : B) = _
        rw [← h1, hX _ (Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out), map_sub, hmul, hmul]
        congr 3
        group
      rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_sub_distrib]
      change _ + (ρ h x ⊗ₜ[Qp] (1 : B) - _) = _
      abel⟩
  have hn : (H.index : LL) ≠ 0 := Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hFf : F ∈ finiteCocycles PD ρ := by
    refine ⟨⟨hF, hFc⟩, (H.index : LL)⁻¹ • y, fun g => ?_⟩
    have := hy g
    change _ = actVB PD ρ g y - y at this
    rw [map_smul, ← smul_sub, ← this, ← Nat.cast_smul_eq_nsmul LL, inv_smul_smul₀ hn]
  have e : (fun g => H.index • (Submodule.Quotient.mk (f₀ g) : V ⧸ L.T)) =
      LinearMap.compLeft L.T.mkQ G F -
        (LinearMap.pi fun g => actD L g - LinearMap.id) (Submodule.Quotient.mk x') := by
    funext g
    have := (Submodule.Quotient.mk_eq_zero L.T).mpr (hx' g)
    change L.T.mkQ _ = 0 at this
    rw [map_sub, map_sub, map_sub, map_nsmul] at this
    change H.index • L.T.mkQ (f₀ g) = L.T.mkQ (F g) - (L.T.mkQ (corHfRepO ρ O g x') - L.T.mkQ x')
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  rw [e]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨F, hFf, rfl⟩)
    (Submodule.mem_sup_right ⟨_, rfl⟩)

end General

theorem corHf_exists_mul_eq_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (n k : ℕ) (hn : n ≠ 0) (hk : padicValNat l n ≤ k) : ∃ u : O, u * (n : O) = ((l ^ k : ℕ) : O) := by
  have hn' : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have : (n : ℤ_[l]) ∣ (l : ℤ_[l]) ^ k := by
    obtain ⟨m, hm⟩ : l ^ padicValNat l n ∣ n := pow_padicValNat_dvd
    have hlm : ¬ l ∣ m := by
      rintro ⟨c, rfl⟩
      apply pow_succ_padicValNat_not_dvd (p := l) hn
      exact ⟨c, by rw [pow_succ, mul_assoc]; exact hm⟩
    have hu : IsUnit (m : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      exact PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlm)
    have e : (n : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l n * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hm
    rw [e, hu.mul_right_dvd]
    exact pow_dvd_pow _ hk
  obtain ⟨c, hc⟩ := this
  refine ⟨algebraMap ℤ_[l] O c, ?_⟩
  have := congrArg (algebraMap ℤ_[l] O) hc
  simp only [map_pow, map_natCast, map_mul] at this
  rw [Nat.cast_pow, this, mul_comm]

theorem corHf_nsmul_mem {O G M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Submodule O (G → M)) (f : G → M) (n m : ℕ) (h : ∃ u : O, u * (n : O) = (m : O))
    (hf : (fun g => n • f g) ∈ S) : (fun g => m • f g) ∈ S := by
  obtain ⟨u, hu⟩ := h
  convert S.smul_mem u hf using 1
  funext g
  rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, smul_smul, hu]

set_option synthInstance.maxHeartbeats 400000 in

theorem pow_smul_mem_HfD_of_restriction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (H : Subgroup ↥(GK K)) [H.Normal] [H.FiniteIndex], IsOpen (H : Set ↥(GK K)) → ∀ (Z f₀ : ↥(GK K) → V.V), ContinuousOn Z H → (∀ g ∈ H, ∀ h ∈ H, Z (g * h) = Z g + V.ρ g (Z h)) → (∃ X : TensorProduct ℚ_[l] V.V P.R.B, ∀ h ∈ H, Z h ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) V.ρ h X - X) → (∀ g h, f₀ (g * h) - (f₀ g + V.ρ g (f₀ h)) ∈ V.L.T) → (∀ h ∈ H, Z h - f₀ h ∈ V.L.T) → ∀ k : ℕ, padicValNat l H.index ≤ k → (fun g => (l ^ k : ℕ) • (Submodule.Quotient.mk (f₀ g) : V.V ⧸ V.L.T)) ∈ HfD (P.PD K) V.L := by
  intro l _ P K LL V H _ _ hH Z f₀ hZ hc hX h₀ hZf k hk
  haveI : IsTopologicalAddGroup V.V := IsModuleTopology.topologicalAddGroup ↥LL.1 V.V
  haveI : ContinuousSMul ↥LL.1 V.V := IsModuleTopology.toContinuousSMul ↥LL.1 V.V
  exact corHf_nsmul_mem _ _ H.index _
    (corHf_exists_mul_eq_pow l _ _ k Subgroup.FiniteIndex.index_ne_zero hk)
    (index_smul_mem_HfD (P.PD K) V.ρ V.L
      (fun g => IsModuleTopology.continuous_of_linearMap (V.ρ g)) V.cont H hH Z f₀ hZ hc hX h₀ hZf)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSameSSOfLattices
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopSteps

theorem reduction_sameSS_of_lattices :
    ∀ {G LL O V : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
      (ρ : Representation LL G V) (L L' : Lattice (O := O) ρ) (lam : O), Irreducible lam →
      SameSS (modRep (latRep L) lam) (modRep (latRep L') lam) :=
  fun _ L L' _ hlam => lattice_reduction_sameSS hlam L L'

end GlobalTheory.TopSteps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerreTateLinearIndependentOfWeightwise
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.SerreTateIndep

variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ} {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)}

theorem chiC_add (i j : ℤ) (g : GQ l) : chiC χ (i + j) g = chiC χ i g * chiC χ j g := by
  simp [chiC, zpow_add]

theorem twAct_twist (i j : ℤ) (g : GQ l) (y : Fin r → PadicComplex l) :
    twAct act χ (i + j) U g y = chiC χ i g • twAct act χ j U g y := by
  unfold twAct
  rw [chiC_add, mul_smul]

theorem twAct_comb {n : ℕ} (i : ℤ) (g : GQ l) (c : Fin n → PadicComplex l)
    (x : Fin n → Fin r → PadicComplex l) :
    twAct act χ i U g (∑ k, c k • x k) = ∑ k, act g (c k) • twAct act χ i U g (x k) := by
  unfold twAct
  have : (fun b => act g ((∑ k, c k • x k) b)) = ∑ k, act g (c k) • fun b => act g (x k b) := by
    funext b; simp [Finset.sum_apply]
  rw [this, Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_smul, smul_comm]

theorem twAct_zero (i : ℤ) (g : GQ l) : twAct act χ i U g 0 = 0 := by
  unfold twAct
  have : (fun b => act g ((0 : Fin r → PadicComplex l) b)) = 0 := by
    funext b; simp
  rw [this, Matrix.mulVec_zero, smul_zero]

theorem linearIndependent_of_weightwise (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (G : Subgroup (GQ l)) (E : IntermediateField ℚ_[l] (Om l))
    (hinv : ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) →
      (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E))
    (r n : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (e : Fin n → Fin r → PadicComplex l) (u : Fin n → ℤ)
    (he : ∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k)
    (hE : ∀ (a : ℤ) (c : Fin n → ↥E), (∀ k, u k ≠ a → c k = 0) →
      ∑ k, (((c k : ↥E) : Om l) : PadicComplex l) • e k = 0 → ∀ k, c k = 0) :
    LinearIndependent (PadicComplex l) e := by
  classical
  have key : ∀ (s : Finset (Fin n)) (c : Fin n → PadicComplex l), (∀ k, k ∉ s → c k = 0) →
      ∑ k, c k • e k = 0 → ∀ k, c k = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro c hc _ k; exact hc k (by simp)
    | insert k0 s hk0 ih =>
      intro c hc hsum
      by_cases h0 : c k0 = 0
      · refine ih c (fun k hk => ?_) hsum
        by_cases hkk : k = k0
        · rw [hkk]; exact h0
        · exact hc k (by simp [hkk, hk])
      exfalso
      set d : Fin n → PadicComplex l := fun k => (c k0)⁻¹ * c k with hd
      have hd0 : d k0 = 1 := inv_mul_cancel₀ h0
      have hds : ∑ k, d k • e k = 0 := by
        simp only [hd, mul_smul]
        rw [← Finset.smul_sum, hsum, smul_zero]
      have hfix : ∀ k, ∀ g ∈ G, chiC χ (u k0 - u k) g * act g (d k) = d k := by
        intro k g hg
        have h1 : ∑ k, (chiC χ (u k0 - u k) g * act g (d k)) • e k = 0 := by
          have h := twAct_comb (act := act) (χ := χ) (U := U) (u k0) g d e
          rw [hds, twAct_zero] at h
          rw [h]
          refine Finset.sum_congr rfl fun k _ => ?_
          conv_rhs => rw [← sub_add_cancel (u k0) (u k), twAct_twist, he g hg k]
          rw [smul_smul, mul_comm]
        have h2 := ih (fun k => chiC χ (u k0 - u k) g * act g (d k) - d k) (fun k hk => ?_) ?_ k
        · exact sub_eq_zero.1 h2
        · by_cases hkk : k = k0
          · subst hkk
            simp [hd0, chiC]
          · have : c k = 0 := hc k (by simp [hkk, hk])
            simp [hd, this]
        · simp only [sub_smul, Finset.sum_sub_distrib, h1, hds, sub_self]
      have hex : ∀ k, ∃ x : ↥E, (((x : ↥E) : Om l) : PadicComplex l) = d k ∧ (u k ≠ u k0 → x = 0) := by
        intro k
        by_cases hu : u k = u k0
        · obtain ⟨x, hx, hxd⟩ := (hinv _ _ (hfix k)).2 (by rw [hu, sub_self])
          exact ⟨⟨x, hx⟩, hxd, fun h => (h hu).elim⟩
        · refine ⟨0, ?_, fun _ => rfl⟩
          rw [(hinv _ _ (hfix k)).1 (sub_ne_zero.2 (Ne.symm hu))]
          simp
      choose x hx hx0 using hex
      have h3 := hE (u k0) x hx0 (by simp only [hx, hds]) k0
      have h4 := hx k0
      rw [h3, hd0] at h4
      simp at h4
  exact Fintype.linearIndependent_iff.2 fun c hc => key Finset.univ c (by simp) hc

end GlobalTheory.SerreTateIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralSqEqOneStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableQuadraticGaussIntegral_sq_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → G₁ ^ 2 = 1 := by
  first | exact @GlobalTheory.JR.WeilQuad.stableGauss_sq_eq_one | exact GlobalTheory.JR.WeilQuad.stableGauss_sq_eq_one | (intros; apply GlobalTheory.JR.WeilQuad.stableGauss_sq_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsCyclotomicTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CyclotomicTowerSubgroupInclusions

variable {l : ℕ} [Fact l.Prime]

theorem unramified_subfield_le_Ks (K : FinExt l) (j : ℕ) : K0 K ≤ Ks K j := le_sup_left

theorem Ks_le_Kinf (K : FinExt l) (j : ℕ) : Ks K j ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ (fun _ hx => Exists.intro j hx)) _

theorem cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified (K : FinExt l) (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup :=
  fun _ hg x => hg ⟨x.1, unramified_subfield_le_Ks K j x.2⟩

theorem Hinf_le_Gj (K : FinExt l) (j : ℕ) : Hinf K ≤ Gj K j :=
  fun _ hg x => hg ⟨x.1, Ks_le_Kinf K j x.2⟩

theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := Iff.rfl

theorem algebraMap_mem_inC (F : IntermediateField ℚ_[l] (Om l)) (u : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) u ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) u, F.algebraMap_mem u, rfl⟩

theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := hg ⟨x, hx⟩
  change g x = x at this
  simp only [ha.1, this]

theorem exists_scale (y : PadicComplex l) : ∃ n : ℕ, ‖(l : PadicComplex l) ^ n * y‖ ≤ 1 := by
  have hl : ‖(l : PadicComplex l)‖ < 1 := by
    have h1 : ‖algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ := norm_algebraMap' _ _
    rw [map_natCast] at h1
    rw [h1]
    exact Padic.norm_p_lt_one
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖y‖
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rwa [norm_mul, norm_pow]⟩

theorem invariants_twist : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ Gj K j, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC (Ks K j)) := by
  intro l _ act χ ha hχ K j hj i y hy
  obtain ⟨hnorm, -, hker⟩ := GlobalTheory.T.cyclotomicCharacterPadic_basic_properties l χ hχ
  obtain ⟨⟨g, hg⟩, -⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ ha hχ K j hj
  obtain ⟨hdec, hdir, -, hmul, hact, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ ha hχ K j hj.1
  obtain ⟨n, hn⟩ := exists_scale y
  have hl0 : (l : PadicComplex l) ^ n ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  set z := (l : PadicComplex l) ^ n * y with hz
  have hzinv : ∀ σ ∈ Gj K j, chiC χ i σ * act σ z = z := by
    intro σ hσ
    rw [hz, map_mul, map_pow, map_natCast, mul_left_comm, hy σ hσ]
  have hzO : z ∈ Ohat K := by
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K z hn).mp fun h hh => ?_
    have h1 : χ h = 1 := (hker K h (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j (Hinf_le_Gj K j hh))).2.mp hh
    have h2 := hzinv h (Hinf_le_Gj K j hh)
    simpa [chiC, h1] using h2
  obtain ⟨a, haK, x, hx, hax⟩ := hdec z hzO
  set c := chiC χ i g with hc
  have hcK : c ∈ inC (Ks K j) := algebraMap_mem_inC _ _
  have hc1 : ‖c‖ = 1 := by
    rw [hc, chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, one_zpow]
  have hga : act g a = a := act_fix ha hg.1 haK.1
  have heq : c * (a + act g x) = a + x := by
    have := hzinv g hg.1
    rwa [hax, map_add, hga] at this
  have hX : x - c * act g x ∈ Xj K j :=
    (Xj K j).sub_mem hx (hmul c ⟨hcK, hc1.le⟩ _ (hact g (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j hg.1) x hx))
  have hK : (c - 1) * a ∈ inC (Ks K j) := by
    rw [mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.sub_mem _ hcK (Subfield.one_mem _)) haK.1
  have h0 : (c - 1) * a = 0 := hdir _ hK _ hX 0 (by linear_combination heq)
  have hrho : 0 < rho1 l :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _
  have hx0 : x = 0 := by
    have h := (GlobalTheory.T.cyclotomic_tower_generator_matrix_perturbation l act χ ha hχ K j hj g hg 1 (fun _ => 1) (by
      intro a b
      rw [Subsingleton.elim a b, Matrix.one_apply_eq]
      refine ⟨?_, by simp⟩
      rw [mem_inC_iff]
      exact Subfield.one_mem _) (by intro a b; simpa using hrho) i).1 (fun _ => x) (fun _ => hx) (by
      funext b
      simp only [twAct, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
      linear_combination heq - h0)
    exact congrFun h 0
  rw [hx0, add_zero] at hax
  refine ⟨fun hi => ?_, fun _ => ?_⟩
  · have hv := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j hj (χ g : ℚ_[l]) hg.2 i hi
    have hne : c - 1 ≠ 0 := by
      intro h
      have h2 : c - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
        rw [hc, chiC, Units.val_zpow_eq_zpow_val, map_sub, map_one]
      rw [h2, map_eq_zero] at h
      rw [h, norm_zero] at hv
      exact (zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos : (0 : ℝ) < l) _).ne hv
    have ha0 : a = 0 := (mul_eq_zero.mp h0).resolve_left hne
    rw [ha0, hz] at hax
    exact (mul_eq_zero.mp hax).resolve_left hl0
  · have : y = ((l : PadicComplex l) ^ n)⁻¹ * a := by
      rw [← hax, hz, inv_mul_cancel_left₀ hl0]
    rw [this, mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (natCast_mem _ l) n)) haK.1

end GlobalTheory.CyclotomicTowerSubgroupInclusions
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltComplexPadicIsAlgClosedUnitBall
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GroundTheory.PAdicHodge

theorem tilt_isAlgClosed_and_unitBall : ∀ (l : ℕ) [Fact l.Prime], IsAlgClosed (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l) ∧ ∃ ι : Fl l →+* (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l), (∀ x, GroundTheory.PAdicHodge.tiltSharp ℂ_[l] l (ι x) = sh x) ∧ (∀ z : (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l), ‖z‖ ≤ 1 → ∃ x, ι x = z) := by
  intro l _
  obtain ⟨e, he⟩ := exists_flEquiv_untilt l
  have hC : IsAlgClosed (Formalism.BasicNotions.Loc.Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  refine ⟨?_, (algebraMap (PreTilt (normInteger ℂ_[l]) l) _).comp (e : Fl l →+* _), ?_, ?_⟩
  · let e' : Formalism.BasicNotions.Loc.Cb l ≃+* Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l :=
      IsFractionRing.ringEquivOfRingEquiv (A := Formalism.BasicNotions.Loc.OCb l) (B := PreTilt (normInteger ℂ_[l]) l) e
    exact IsAlgClosed.of_ringEquiv _ _ e'
  · intro x
    rw [RingHom.comp_apply, tiltSharp_algebraMap]
    exact he x
  · intro z hz
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hz
    exact ⟨e.symm a, by simp⟩

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCocycleUniformizerPowSmulMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionCocycle_uniformizer_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', ∃ r : ℕ, ∀ g, (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T := by
  first | exact @GlobalTheory.TorsCoc.cocycle_pow_smul_mem | exact GlobalTheory.TorsCoc.cocycle_pow_smul_mem | (intros; apply GlobalTheory.TorsCoc.cocycle_pow_smul_mem <;> assumption)
end

