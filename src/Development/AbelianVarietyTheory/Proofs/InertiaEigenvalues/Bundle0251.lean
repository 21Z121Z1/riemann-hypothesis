import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0237
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfPolyPow
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPolyPow

theorem aeval_mul_apply {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (p q : L[X]) (x : M) : Polynomial.aeval f (p * q) x = Polynomial.aeval f p (Polynomial.aeval f q x) := by
  rw [map_mul, Module.End.mul_apply]

theorem eigen_of_pow_of_separable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (c : L) (m : ℕ) (r : L[X]) (hr : r.Separable) (x : M)
    (h1 : Polynomial.aeval f ((X - C c) ^ m) x = 0) (h2 : Polynomial.aeval f r x = 0) :
    Polynomial.aeval f (X - C c) x = 0 := by
  obtain ⟨t, hrt, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr.ne_zero c
  have hle := Polynomial.rootMultiplicity_le_one_of_separable hr c
  have hcop : IsCoprime ((X - C c) ^ m) t :=
    ((Polynomial.irreducible_X_sub_C c).coprime_iff_not_dvd.2 hnd).pow_left
  obtain ⟨A, B', hAB⟩ := hcop
  have hs : ∃ s : L[X], (X - C c) * t = s * r := by
    interval_cases hj : r.rootMultiplicity c
    · exact ⟨X - C c, by rw [hrt]; ring⟩
    · exact ⟨1, by rw [hrt]; ring⟩
  obtain ⟨s, hs⟩ := hs
  have : (X - C c) = (A * (X - C c)) * (X - C c) ^ m + (B' * s) * r := by
    rw [mul_assoc (B') s r, ← hs]
    linear_combination (-(X - C c)) * hAB
  rw [this, map_add, LinearMap.add_apply, aeval_mul_apply, h1, map_zero, aeval_mul_apply, h2, map_zero, add_zero]

theorem mem_iSup_eigen_pow {L M ι : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (r : L[X]) (hr : r.Separable)
    (hrD : ∀ x ∈ D, Polynomial.aeval f r x = 0) (c : ι → L) (m : ℕ) (s : Finset ι) :
    (∀ a ∈ s, ∀ b ∈ s, c a = c b → a = b) → ∀ d ∈ D,
      Polynomial.aeval f ((∏ a ∈ s, (X - C (c a))) ^ m) d = 0 →
      d ∈ ⨆ a ∈ s, (D ⊓ LinearMap.ker (f - c a • LinearMap.id)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ d _ h
    simp at h
    simp [h]
  | insert a t hat ih =>
    intro hinj d hd h
    rw [Finset.prod_insert hat, mul_pow] at h
    have hcop : IsCoprime ((X - C (c a)) ^ m) ((∏ b ∈ t, (X - C (c b))) ^ m) := by
      refine IsCoprime.pow (IsCoprime.prod_right fun b hb => ?_)
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.2 fun e => hat ?_))
      rw [hinj a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) e]
      exact hb
    obtain ⟨u, v, huv⟩ := hcop
    set Q := (∏ b ∈ t, (X - C (c b))) ^ m with hQ
    have hdec : d = Polynomial.aeval f (u * (X - C (c a)) ^ m) d + Polynomial.aeval f (v * Q) d := by
      rw [← LinearMap.add_apply, ← map_add, huv, map_one, Module.End.one_apply]
    rw [Finset.iSup_insert, hdec, add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · have hmem := GlobalTheory.PassPoly.aeval_mem_of_stable f D hD (v * Q) d hd
      refine ⟨hmem, ?_⟩
      have h1 : Polynomial.aeval f ((X - C (c a)) ^ m) (Polynomial.aeval f (v * Q) d) = 0 := by
        rw [← aeval_mul_apply, show (X - C (c a)) ^ m * (v * Q) = v * ((X - C (c a)) ^ m * Q) by ring,
          aeval_mul_apply, h, map_zero]
      have := eigen_of_pow_of_separable f (c a) m r hr _ h1 (hrD _ hmem)
      simpa [Module.algebraMap_end_apply] using this
    · refine ih (fun x hx y hy => hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)) _
        (GlobalTheory.PassPoly.aeval_mem_of_stable f D hD _ d hd) ?_
      rw [← aeval_mul_apply, show Q * (u * (X - C (c a)) ^ m) = u * ((X - C (c a)) ^ m * Q) by ring,
        aeval_mul_apply, h, map_zero]

section
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_pow (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    (actVB PC.PD ρ g ^ n) x = actVB PC.PD ρ (g ^ n) x := by
  induction n generalizing x with
  | zero => simp [GlobalTheory.PassPoly.actVB_one']
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, GlobalTheory.PassPoly.actVB_mul']

theorem aeval_index_kill (g : G) : ∀ x ∈ PC.Dpcris ρ,
    Polynomial.aeval (actVB PC.PD ρ g) (X ^ PC.H.index - C (1 : LL)) x = 0 := by
  intro x hx
  haveI := PC.normal
  have hg : g ^ PC.H.index ∈ PC.H := Subgroup.pow_index_mem PC.H g
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply]
  rw [actVB_pow, (GlobalTheory.PassPoly.mem_Dpcris_iff PC ρ x).1 hx _ hg, sub_self]

theorem separable_index [CharZero LL] : (X ^ PC.H.index - C (1 : LL)).Separable := by
  haveI := PC.finiteIndex
  exact Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero) one_ne_zero

theorem inertiaThrough_of_poly_pow [CharZero LL] (Sig : Finset (PC.Iner →* LLˣ))
    (h1 : ∀ a ∈ Sig, ∀ g : PC.Iner, (g : G) ∈ PC.H → a g = 1)
    (h2 : ∀ a ∈ Sig, Nat.Coprime (orderOf a) PC.PD.p)
    (h3 : ∀ (g : PC.Iner), ∃ m : ℕ, ∀ d ∈ PC.Dpcris ρ, (Polynomial.aeval (actVB PC.PD ρ (g : G))
      ((∏ a ∈ Sig, (X - C ((a g : LLˣ) : LL))) ^ m)) d = 0)
    (h4 : ∃ γ : PC.Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧
      ∀ g : PC.Iner, ∃ (n : ℕ) (u : PC.Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) :
    PC.InertiaThrough ρ Sig := by

  have htriv : ∀ u : PC.Iner, (∀ a ∈ Sig, a u = 1) → ∀ x ∈ PC.Dpcris ρ,
      actVB PC.PD ρ (u : G) x = x := by
    intro u hu x hx
    obtain ⟨m, hm⟩ := h3 u
    have hprod : (∏ a ∈ Sig, (X - C ((a u : LLˣ) : LL))) ^ m = (X - C (1 : LL)) ^ (Sig.card * m) := by
      rw [Finset.prod_congr rfl (fun a ha => by rw [hu a ha, Units.val_one]), Finset.prod_const, pow_mul]
    have hk := hm x hx
    rw [hprod] at hk
    have := eigen_of_pow_of_separable _ 1 _ _ (separable_index PC) x hk (aeval_index_kill PC ρ _ x hx)
    simpa [Module.algebraMap_end_apply, sub_eq_zero] using this
  refine ⟨h1, h2, le_antisymm ?_ ?_⟩
  · obtain ⟨γ, hsep, hgen⟩ := h4
    intro d hd
    obtain ⟨m, hm⟩ := h3 γ
    have := mem_iSup_eigen_pow (actVB PC.PD ρ (γ : G)) (PC.Dpcris ρ) (GlobalTheory.PassPoly.Dpcris_stable PC ρ γ)
      _ (separable_index PC) (aeval_index_kill PC ρ _)
      (fun a : PC.Iner →* LLˣ => ((a γ : LLˣ) : LL)) m Sig
      (fun a ha b hb e => hsep a ha b hb (Units.ext e)) d hd (hm d hd)
    refine (iSup₂_mono (fun a ha => ?_) : _ ≤ ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a) this
    rintro x ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have hγ : actVB PC.PD ρ (γ : G) x = ((a γ : LLˣ) : LL) • x := by
      simpa [sub_eq_zero] using hx'
    have hn : ∀ n : ℕ, actVB PC.PD ρ ((γ : G) ^ n) x = ((a γ : LLˣ) : LL) ^ n • x := by
      intro n
      induction n with
      | zero => simp [GlobalTheory.PassPoly.actVB_one']
      | succ n ih => rw [pow_succ, GlobalTheory.PassPoly.actVB_mul', hγ, map_smul, ih, smul_smul, pow_succ, mul_comm]
    simp only [Submodule.coe_iInf, Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro g
    obtain ⟨n, u, hu, rfl⟩ := hgen g
    rw [map_mul, hu a ha, mul_one, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, GlobalTheory.PassPoly.actVB_mul',
      htriv u hu x hx, hn, Units.val_pow_eq_pow_val]
  · exact iSup₂_le fun a _ => inf_le_left

end

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) l) → (∀ (g : (pc P h hN hF hS).Iner), ∃ m : ℕ, ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, (Polynomial.aeval (actVB (P.PD K) ρ (g : ↥(GK K))) ((∏ a ∈ Sig, (X - C ((a g : (↥LL.1)ˣ) : ↥LL.1))) ^ m)) d = 0) → (∃ γ : (pc P h hN hF hS).Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧ ∀ g : (pc P h hN hF hS).Iner, ∃ (n : ℕ) (u : (pc P h hN hF hS).Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) → (pc P h hN hF hS).InertiaThrough ρ Sig := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ Sig h1 h2 h3 h4
  haveI : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  refine inertiaThrough_of_poly_pow (pc P h hN hF hS) ρ Sig h1 ?_ h3 h4
  have hp : (pc P h hN hF hS).PD.p = l := P.PD_p K
  rw [hp]
  exact h2

end GlobalTheory.PassPolyPow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersLevelOneEqSumZetaPow
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.Cyc.FirstLevel

open Polynomial GlobalTheory.Cyc.IntBasis

variable {l : ℕ} [Fact l.Prime]

private theorem norm_primitiveRoot_sub_one' (ζ : Om l) (hζ : IsPrimitiveRoot ζ l) :
    ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) - 1)) := by
  have h1 : IsPrimitiveRoot (algebraMap (Om l) (PadicComplex l) ζ) (l ^ 1) := by
    rw [pow_one]
    exact hζ.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  have h2 := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl _ h1
  have h3 : ‖algebraMap (Om l) (PadicComplex l) (ζ - 1)‖ = ‖ζ - 1‖ :=
    PadicComplex.norm_extends l (ζ - 1)
  rw [map_sub, map_one, h2] at h3
  rw [← h3]
  simp

theorem norm_term (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (z : Om l) (hz : z ∈ K0 K) (h0 : z ≠ 0) :
    ∃ n : ℤ, ‖z‖ = (l : ℝ) ^ n ∧ ∀ a : ℕ, ‖z * (ζ - 1) ^ a‖ =
        (l : ℝ) ^ (((n * (l - 1) - a : ℤ) : ℝ) / ((l : ℝ) - 1)) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hl0 : (0 : ℝ) < l := by linarith
  have hm : (l : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K z hz h0
  refine ⟨n, hn, fun a => ?_⟩
  rw [norm_mul, norm_pow, hn, norm_primitiveRoot_sub_one' ζ hζ, ← Real.rpow_intCast,
    ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_add hl0]
  congr 1
  push_cast
  field_simp
  try ring

theorem term_le (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (z : ℕ → Om l) (hz : ∀ a, z a ∈ K0 K) (a : ℕ) (ha : a < l - 1) :
    ‖z a * (ζ - 1) ^ a‖ ≤ ‖∑ b ∈ Finset.range (l - 1), z b * (ζ - 1) ^ b‖ := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hm : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  refine norm_le_norm_sum (Finset.range (l - 1)) (fun b => z b * (ζ - 1) ^ b) ?_ a
    (Finset.mem_range.2 ha)
  intro b hb c hc hbc hb0 hc0 heq
  have hb' : z b ≠ 0 := fun h => hb0 (by simp [h])
  have hc' : z c ≠ 0 := fun h => hc0 (by simp [h])
  have heq' : ‖z b * (ζ - 1) ^ b‖ = ‖z c * (ζ - 1) ^ c‖ := heq
  obtain ⟨nb, -, hnb⟩ := GlobalTheory.Cyc.FirstLevel.norm_term K ζ hζ (z b) (hz b) hb'
  obtain ⟨nc, -, hnc⟩ := GlobalTheory.Cyc.FirstLevel.norm_term K ζ hζ (z c) (hz c) hc'
  rw [hnb b, hnc c] at heq'
  have he := le_antisymm ((Real.rpow_le_rpow_left_iff hl1).1 heq'.le)
    ((Real.rpow_le_rpow_left_iff hl1).1 heq'.ge)
  rw [div_left_inj' hm.ne'] at he
  have he' : nb * ((l : ℤ) - 1) - b = nc * ((l : ℤ) - 1) - c := by exact_mod_cast he
  rw [Finset.mem_range] at hb hc
  have hb2 : (b : ℤ) < (l : ℤ) - 1 := by omega
  have hc2 : (c : ℤ) < (l : ℤ) - 1 := by omega
  have hb3 : (0 : ℤ) ≤ b := by omega
  have hc3 : (0 : ℤ) ≤ c := by omega
  have hm' : (0 : ℤ) ≤ (l : ℤ) - 1 := by omega
  apply hbc
  rcases lt_trichotomy nb nc with h | h | h
  · exfalso
    nlinarith [mul_le_mul_of_nonneg_right (show nb + 1 ≤ nc by omega) hm']
  · subst h
    have : (b : ℤ) = c := by linarith
    exact_mod_cast this
  · exfalso
    nlinarith [mul_le_mul_of_nonneg_right (show nc + 1 ≤ nb by omega) hm']

theorem coeff_le (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (z : Om l) (hz : z ∈ K0 K) (a : ℕ) (ha : a < l - 1) (h : ‖z * (ζ - 1) ^ a‖ ≤ 1) :
    ‖z‖ ≤ 1 := by
  by_cases h0 : z = 0
  · rw [h0, norm_zero]
    exact zero_le_one
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hm : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  obtain ⟨n, hn, hna⟩ := GlobalTheory.Cyc.FirstLevel.norm_term K ζ hζ z hz h0
  rw [hna a] at h
  have h' := (Real.rpow_le_rpow_left_iff hl1).1 (h.trans_eq (Real.rpow_zero (l : ℝ)).symm)
  rw [div_le_iff₀ hm, zero_mul] at h'
  have key : n * ((l : ℤ) - 1) - a ≤ 0 := by exact_mod_cast h'
  have ha' : (a : ℤ) < (l : ℤ) - 1 := by omega
  have hn0 : n ≤ 0 := by
    by_contra hc
    have hm' : (0 : ℤ) ≤ (l : ℤ) - 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ n by omega) hm']
  rw [hn]
  exact zpow_le_one_of_nonpos₀ hl1.le hn0

theorem exists_poly (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (x : Om l) (hx : x ∈ Ks K 1) :
    ∃ p : (↥(K0 K))[X], p.natDegree < l - 1 ∧ aeval ζ p = x := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have : NeZero l := ⟨by omega⟩
  have hint : IsIntegral (↥(K0 K)) ζ := by
    refine IsIntegral.of_pow (n := l) (by omega) ?_
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  have hle : Ks K 1 ≤ (IntermediateField.adjoin (↥(K0 K)) {ζ}).restrictScalars ℚ_[l] := by
    unfold Ks
    refine sup_le ?_ ?_
    · intro y hy
      rw [IntermediateField.mem_restrictScalars]
      exact IntermediateField.algebraMap_mem _ (⟨y, hy⟩ : ↥(K0 K))
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hy' : y ^ l = 1 := by simpa using hy
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy'
      rw [SetLike.mem_coe, IntermediateField.mem_restrictScalars]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self _ ζ) i
  have hx' : x ∈ (IntermediateField.adjoin (↥(K0 K)) {ζ}).toSubalgebra :=
    (IntermediateField.mem_restrictScalars ℚ_[l]).1 (hle hx)
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx'
  obtain ⟨p, rfl⟩ := hx'
  have hmon := minpoly.monic hint
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly (↥(K0 K)) ζ).natDegree ≤ l - 1 := by
    have hdvd : minpoly (↥(K0 K)) ζ ∣ Polynomial.cyclotomic l (↥(K0 K)) := by
      apply minpoly.dvd
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
      exact hζ.isRoot_cyclotomic (by omega)
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.cyclotomic_ne_zero l (↥(K0 K)))
    rwa [Polynomial.natDegree_cyclotomic, Nat.totient_prime (Fact.out : l.Prime)] at this
  refine ⟨p %ₘ minpoly (↥(K0 K)) ζ, ?_, ?_⟩
  · have hne : minpoly (↥(K0 K)) ζ ≠ 1 := by
      intro h
      rw [h, Polynomial.natDegree_one] at hpos
      exact lt_irrefl 0 hpos
    exact lt_of_lt_of_le (Polynomial.natDegree_modByMonic_lt p hmon hne) hdeg
  · exact Polynomial.aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)

end GlobalTheory.Cyc.FirstLevel

open Polynomial GlobalTheory.Cyc.IntBasis in

theorem GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : Om l), IsPrimitiveRoot ζ l → ∀ α : Om l, α ∈ Ks K 1 → ‖α‖ ≤ 1 → ∃ y : Fin l → Om l, (∀ a, y a ∈ K0 K ∧ ‖y a‖ ≤ 1) ∧ α = ∑ a : Fin l, ζ ^ (a : ℕ) * y a := by
  intro l _ K ζ hζ α hα hα1
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨p, hpdeg, hp⟩ := GlobalTheory.Cyc.FirstLevel.exists_poly K ζ hζ α hα
  set q := Polynomial.taylor (1 : ↥(K0 K)) p with hq
  have hqdeg : q.natDegree < l - 1 := by
    rw [hq, Polynomial.natDegree_taylor]
    exact hpdeg
  let z : ℕ → Om l := fun b => ((q.coeff b : ↥(K0 K)) : Om l)
  have hzK : ∀ b, z b ∈ K0 K := fun b => (q.coeff b).2
  have hsum : α = ∑ b ∈ Finset.range (l - 1), z b * (ζ - 1) ^ b := by
    rw [← hp]
    have h1 : aeval ζ p = aeval (ζ - 1) q := by
      rw [hq, aeval_taylor']
      congr 1
      simp
    rw [h1, Polynomial.aeval_eq_sum_range' hqdeg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Algebra.smul_def]
    rfl
  have hzle : ∀ b, ‖z b‖ ≤ 1 := by
    intro b
    by_cases hb : b < l - 1
    · apply GlobalTheory.Cyc.FirstLevel.coeff_le K ζ hζ (z b) (hzK b) b hb
      calc ‖z b * (ζ - 1) ^ b‖ ≤ ‖∑ c ∈ Finset.range (l - 1), z c * (ζ - 1) ^ c‖ :=
            GlobalTheory.Cyc.FirstLevel.term_le K ζ hζ z hzK b hb
        _ = ‖α‖ := by rw [← hsum]
        _ ≤ 1 := hα1
    · have hc : q.coeff b = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [z, hc]
  let Q : (intRing (K0 K))[X] := ∑ b ∈ Finset.range (l - 1),
    Polynomial.C (⟨z b, ⟨hzK b, hzle b⟩⟩ : intRing (K0 K)) * (Polynomial.X - Polynomial.C 1) ^ b
  have hQdeg : Q.natDegree < l := by
    have : Q.natDegree ≤ l - 2 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro b hb
      rw [Finset.mem_range] at hb
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      refine Polynomial.natDegree_pow_le.trans ?_
      rw [Polynomial.natDegree_X_sub_C]
      omega
    omega
  have hQ : aeval ζ Q = α := by
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, Polynomial.aeval_C, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      map_one]
    rfl
  have hmem : ∀ s : intRing (K0 K), (s : Om l) ∈ K0 K ∧ ‖(s : Om l)‖ ≤ 1 := fun s => s.2
  refine ⟨fun a : Fin l => ((Q.coeff (a : ℕ) : intRing (K0 K)) : Om l),
    fun a => hmem _, ?_⟩
  rw [← hQ, Polynomial.aeval_eq_sum_range' hQdeg, Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Algebra.smul_def, mul_comm]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeComapOfExactFlat
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory

theorem isBaseChange_comap_of_exact (A E : Type) [CommRing A] [CommRing E] [Algebra A E]
    [Module.Flat A E] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂]
    [Module E D₀] [Module E D₁] [Module E D₂] [Module A D₀] [Module A D₁] [Module A D₂]
    [IsScalarTower A E D₀] [IsScalarTower A E D₁] [IsScalarTower A E D₂]
    (j : D₀ →ₗ[E] D₁) (q : D₁ →ₗ[E] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂)
    (hj : Function.Injective j) (hex : Function.Exact j q) (_hq : Function.Surjective q)
    (h₁ : IsBaseChange E N₁.subtype) (h₂ : IsBaseChange E N₂.subtype)
    (hN : ∀ x ∈ N₁, q x ∈ N₂) :
    IsBaseChange E (N₁.comap (j.restrictScalars A)).subtype := by
  set N₀ := N₁.comap (j.restrictScalars A) with hN₀
  let ι : N₀ →ₗ[A] N₁ := (j.restrictScalars A).restrict (fun x hx => hx)
  let f : N₁ →ₗ[A] N₂ := (q.restrictScalars A).restrict hN
  have hιv : ∀ y : N₀, (ι y : D₁) = j y := fun _ => rfl
  have hfv : ∀ y : N₁, (f y : D₂) = q y := fun _ => rfl
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply hj
    have := congrArg Subtype.val hxy
    simpa [ι] using this
  have hιf : Function.Exact ι f := by
    intro y
    constructor
    · intro hy
      have hy' : q (y : D₁) = 0 := by
        have := congrArg Subtype.val hy
        rwa [hfv] at this
      obtain ⟨x, hx⟩ := (hex (y : D₁)).1 hy'
      refine ⟨⟨x, ?_⟩, ?_⟩
      · show j x ∈ N₁
        rw [hx]; exact y.2
      · apply Subtype.ext
        simpa [ι] using hx
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      simp only [f, ι, LinearMap.restrict_apply, LinearMap.restrictScalars_apply,
        ZeroMemClass.coe_zero]
      exact (hex (j x)).2 ⟨x, rfl⟩
  have hιT : Function.Injective (LinearMap.lTensor E ι) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι hι
  have hfT : Function.Exact (LinearMap.lTensor E ι) (LinearMap.lTensor E f) :=
    Module.Flat.lTensor_exact E hιf
  let Φ : E ⊗[A] N₀ →ₗ[E] D₀ := N₀.subtype.liftBaseChange E
  have hcomm₁ : ∀ t : E ⊗[A] N₀, j (Φ t) = h₁.equiv (LinearMap.lTensor E ι t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Φ, IsBaseChange.equiv_tmul, hιv]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hcomm₂ : ∀ t : E ⊗[A] N₁, h₂.equiv (LinearMap.lTensor E f t) = q (h₁.equiv t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [IsBaseChange.equiv_tmul, hfv]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hΦi : Function.Injective Φ := by
    intro s t hst
    apply hιT
    apply h₁.equiv.injective
    rw [← hcomm₁, ← hcomm₁, hst]
  have hΦs : Function.Surjective Φ := by
    intro d
    obtain ⟨t, ht⟩ := h₁.equiv.surjective (j d)
    have h0 : LinearMap.lTensor E f t = 0 := by
      apply h₂.equiv.injective
      rw [hcomm₂, ht, map_zero]
      exact (hex (j d)).2 ⟨d, rfl⟩
    obtain ⟨s, hs⟩ := (hfT t).1 h0
    refine ⟨s, hj ?_⟩
    rw [hcomm₁, hs, ht]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩) ?_
  intro x
  show Φ (1 ⊗ₜ x) = x
  simp [Φ, LinearMap.liftBaseChange_tmul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundaryStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (z : G → Fin A.m → k) (b g : ZMod n → Vc k A.m), Repr F A z b g → (b, g) ∈ herrB (F.D A) → z ∈ cob A := by
  first | exact @GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB | exact GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB | (intros; apply GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSenWeightMemWeightResiduesStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_senWeight_mem_weight_residues : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.Ut i, ((u - Dt.w i : ℤ) : k) = x := by
  first | exact @GlobalTheory.Models.model_sen_mem | exact GlobalTheory.Models.model_sen_mem | (intros; apply GlobalTheory.Models.model_sen_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l k : ℕ), l.Prime → 1 ≤ k → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ ζ : O, IsPrimitiveRoot ζ (l ^ k) → ζ - 1 ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (ζ - 1) = 1 / (Nat.totient (l ^ k) : ℝ) := by
  first | exact @GlobalTheory.nval_primitiveRoot_prime_pow_sub_one | exact GlobalTheory.nval_primitiveRoot_prime_pow_sub_one | (intros; apply GlobalTheory.nval_primitiveRoot_prime_pow_sub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSubSubMemXiOfMonodromyEqStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_sub_sub_mem_xi_of_monodromy_eq : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, ∀ σ : Vec K a ι, D.conn σ = D.zeta y → ∃ d : D.D, D.phi σ - σ - D.phi y = D.xi d := by
  first | exact @GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi | exact GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi | (intros; apply GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi <;> assumption)
end

