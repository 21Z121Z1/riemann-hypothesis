import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0016
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusMemPullbackOfInvariant
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem letE_mul_self_eq (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  unfold letE
  rw [← Pi.single_mul, mul_one]

theorem idempotent_smul_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (x : W.DD T) : (letE i : LetA O n) • (letE i : LetA O n) • x = (letE i : LetA O n) • x := by
  rw [smul_smul, letE_mul_self_eq]

private theorem phiD_letA_smul_eq_phiA_smul_phiD (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul] <;> rfl

private theorem phiA_letE_sub_one_eq_letE (W : LocWach PD LL O v n) (i : ZMod n) :
    W.φA (letE (i - 1) : LetA O n) = letE i := by
  funext j
  show W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h
    simp [letE]
  · have h' : j - 1 ≠ i - 1 := fun e => h (sub_left_inj.mp e)
    simp [letE, Pi.single_apply, h, h']

theorem frobenius_idempotent_shift (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE (i - 1) : LetA O n) • x) = (letE i : LetA O n) • W.φD T x := by
  rw [phiD_letA_smul_eq_phiA_smul_phiD, phiA_letE_sub_one_eq_letE]

private theorem letGamma_letE_eq_letE (W : LocWach PD LL O v n) (g : W.Gam) (i : ZMod n) :
    letγ (W.γ₀ g) (letE i : LetA O n) = letE i := by
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h
    simp [letE]
  · simp [letE, Pi.single_apply, h]

theorem gammaD_idempotent_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) : W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul,
    letGamma_letE_eq_letE]

theorem natCast_pow_smul_eq_algebra (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : O) ^ N • x = ((PD.p : ℕ) : LetA O n) ^ N • x := by
  rw [← algebraMap_smul (LetA O n) (((PD.p : ℕ) : O) ^ N) x, map_pow, map_natCast]

theorem frobeniusA_natCast_pow (W : LocWach PD LL O v n) (N : ℕ) :
    W.φA (((PD.p : ℕ) : LetA O n) ^ N) = ((PD.p : ℕ) : LetA O n) ^ N := by
  rw [map_pow, map_natCast]

theorem gammaA_natCast_pow (W : LocWach PD LL O v n) (g : W.Gam) (N : ℕ) :
    W.γA g (((PD.p : ℕ) : LetA O n) ^ N) = ((PD.p : ℕ) : LetA O n) ^ N := by
  rw [map_pow, map_natCast]

theorem basis_vector_eq_zero_or_torsionFree (W : LocWach PD LL O v n) (e : W.DD W.one)
    (hspan : W.N W.one = Submodule.span (LetA O n) {e}) (π' : LetA O n)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W W.one π') : e = 0 ∨ ∀ β : LetA O n, β • e = 0 → β = 0 := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hm
  by_cases he : e = 0
  · exact Or.inl he
  right
  intro β hβ
  have heN : e ∈ W.N W.one := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self e
  have hkill : ∀ y ∈ W.N W.one, β • y = 0 := by
    intro y hy
    rw [hspan] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_smul, mul_comm, ← smul_smul, hβ, smul_zero]
  obtain ⟨a, ha, hu⟩ := huniq e heN
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      exact (he (by simpa using ha)).elim
    · exact h0
  have hz : ∑ j, β • b j = 0 := Finset.sum_eq_zero fun j _ => hkill _ (hb j).1
  have h2 : e = ∑ j, (a j + β) • b j := by
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← ha, hz, add_zero]
  have h3 := congrFun (hu (fun j => a j + β) h2) ⟨0, hr⟩
  simpa using h3

theorem eq_zero_of_natCast_pow_mul (hζ : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p)
    (hO : ∃ _ : IsDomain O, IsDiscreteValuationRing O ∧ IsFractionRing O LL) (N : ℕ) (β : LetA O n)
    (h : ((PD.p : ℕ) : LetA O n) ^ N * β = 0) : β = 0 := by
  obtain ⟨hd, -, hf⟩ := hO
  haveI := hd
  haveI : NeZero PD.p := ⟨PD.hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hζ
  have hLL : ((PD.p : ℕ) : LL) ≠ 0 := hζ.neZero'.out
  have hpO : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h0
    apply hLL
    rw [← map_natCast (algebraMap O LL), h0, map_zero]
  have hpS : ((PD.p : ℕ) : PowerSeries O) ≠ 0 := by
    intro h0
    apply hpO
    have h1 := congrArg PowerSeries.constantCoeff h0
    rwa [map_natCast, map_zero] at h1
  funext j
  have hj := congrFun h j
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Pi.zero_apply] at hj
  rcases mul_eq_zero.mp hj with h1 | h1
  · exact ((pow_ne_zero N hpS) h1).elim
  · exact h1

theorem frobenius_mem_pullback_of_invariant (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' : LetA O n)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π') (i : ZMod n) (t : W.DD T) (ht : t ∈ W.N T)
    (hl : (letE (i - 1) : LetA O n) • t = t) : W.φD T t ∈ pullJ W T (i - 1) 1 := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hm
  obtain ⟨a, ha, -⟩ := huniq t ht
  have ht' : t = ∑ j, a j • ((letE (i - 1) : LetA O n) • b j) := by
    calc t = (letE (i - 1) : LetA O n) • t := hl.symm
      _ = (letE (i - 1) : LetA O n) • ∑ j, a j • b j := by rw [← ha]
      _ = _ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, smul_smul, mul_comm]
  rw [ht', map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [phiD_letA_smul_eq_phiA_smul_phiD]
  apply Submodule.smul_mem
  unfold pullJ
  apply Submodule.subset_span
  refine ⟨(letE (i - 1) : LetA O n) • b j,
    ⟨(W.N T).smul_mem _ (hb j).1, idempotent_smul_smul W T (i - 1) (b j), fun δ hδ => ?_⟩, ?_⟩
  · rw [gammaD_idempotent_smul, (hb j).2 δ hδ]
  · simp

private theorem locWach_map_letA_smul_comm (W : LocWach PD LL O v n) {T Y : LocLat G Qp LL O}
    (f : LatHom T.L Y.L) (a : LetA O n) (x : W.DD T) : W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

theorem pullback_span_of_exact (W : LocWach PD LL O v n) {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L)
    (π : LatHom Y.L W.one.L) (hY : IsCrys PD Y.ρ) (hO : IsCrys PD W.one.ρ)
    (hker : ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x) (hsat : ∀ x, W.map ι x ∈ W.N Y → x ∈ W.N T)
    (hinj : Function.Injective (W.map ι)) (π' : LetA O n) (hmT : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (e' : W.DD W.one) (hspan : W.N W.one = Submodule.span (LetA O n) {e'}) (i : ZMod n) (N : ℕ)
    (ε : W.DD Y) (hεN : ε ∈ W.N Y)
    (hεπ : W.map π ε = ((PD.p : ℕ) : LetA O n) ^ N • (letE (i - 1) : LetA O n) • e') :
    ∀ x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Y (W.Nl Y (i - 1)), ∃ p ∈ pullJ W T (i - 1) 1, ∃ β : LetA O n,
      ((PD.p : ℕ) : LetA O n) ^ N • x = W.map ι p + β • W.φD Y ε ∧ (e' = 0 → β = 0) := by
  intro x hx
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z0, hz0, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := (hz0 : z0 ∈ (W.N Y).map ((letE (i - 1) : LetA O n) • LinearMap.id))
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    set z : W.DD Y := (letE (i - 1) : LetA O n) • y with hzdef
    have hz_idem : (letE (i - 1) : LetA O n) • z = z := by
      rw [hzdef]
      exact idempotent_smul_smul W Y (i - 1) y
    have hzN : z ∈ W.N Y := (W.N Y).smul_mem _ hy
    have hπz := W.map_N π hY hO z hzN
    obtain ⟨c, hc, hc0⟩ : ∃ c : LetA O n, c • e' = W.map π z ∧ (e' = 0 → c = 0) := by
      by_cases he : e' = 0
      · rw [hspan, he, Submodule.span_zero_singleton, Submodule.mem_bot] at hπz
        exact ⟨0, by rw [zero_smul, hπz], fun _ => rfl⟩
      · rw [hspan] at hπz
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hπz
        exact ⟨c, hc, fun h => (he h).elim⟩
    have hπlet : W.map π z = (letE (i - 1) : LetA O n) • W.map π z := by
      rw [← locWach_map_letA_smul_comm, hz_idem]
    have hce : c • e' = ((letE (i - 1) : LetA O n) * c) • e' := by
      rw [← smul_smul, hc]
      exact hπlet
    have hw : W.map π (((PD.p : ℕ) : LetA O n) ^ N • z - c • ε) = 0 := by
      rw [map_sub, locWach_map_letA_smul_comm W π _ z, locWach_map_letA_smul_comm W π c ε, hεπ, ← hc, hce]
      simp only [smul_smul]
      rw [sub_eq_zero]
      congr 1
      ring
    obtain ⟨y', hy'⟩ := (hker _).mp hw
    have hι : W.map ι ((letE (i - 1) : LetA O n) • y') =
        ((PD.p : ℕ) : LetA O n) ^ N • z - c • ((letE (i - 1) : LetA O n) • ε) := by
      rw [locWach_map_letA_smul_comm, hy', smul_sub, smul_comm (letE (i - 1) : LetA O n) _ z, hz_idem,
        smul_comm (letE (i - 1) : LetA O n) c ε]
    have hyN : (letE (i - 1) : LetA O n) • y' ∈ W.N T := by
      apply hsat
      rw [hι]
      exact sub_mem ((W.N Y).smul_mem _ hzN) ((W.N Y).smul_mem _ ((W.N Y).smul_mem _ hεN))
    have hp := frobenius_mem_pullback_of_invariant W T π' hmT i _ hyN (idempotent_smul_smul W T (i - 1) y')
    have e1 : W.φD Y (((PD.p : ℕ) : LetA O n) ^ N • z) = ((PD.p : ℕ) : LetA O n) ^ N • W.φD Y z := by
      rw [phiD_letA_smul_eq_phiA_smul_phiD, frobeniusA_natCast_pow]
    have e2 : W.φD Y (c • (letE (i - 1) : LetA O n) • ε) =
        (W.φA c * (letE i : LetA O n)) • W.φD Y ε := by
      rw [phiD_letA_smul_eq_phiA_smul_phiD, frobenius_idempotent_shift, smul_smul]
    refine ⟨_, hp, W.φA c * (letE i : LetA O n), ?_, fun h => by rw [hc0 h, map_zero, zero_mul]⟩
    rw [W.map_φ, hι, map_sub, e1, e2, sub_add_cancel]
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp, fun _ => rfl⟩
  | add a b _ _ ha hb =>
    obtain ⟨q1, hq1, β1, h11, h21⟩ := ha
    obtain ⟨q2, hq2, β2, h12, h22⟩ := hb
    refine ⟨q1 + q2, Submodule.add_mem _ hq1 hq2, β1 + β2, ?_, fun h => by rw [h21 h, h22 h, add_zero]⟩
    rw [smul_add, h11, h12, map_add, add_smul]
    abel
  | smul c a _ ha =>
    obtain ⟨q, hq, β, h1, h2⟩ := ha
    refine ⟨c • q, Submodule.smul_mem _ _ hq, c * β, ?_, fun h => by rw [h2 h, mul_zero]⟩
    rw [smul_comm, h1, smul_add, locWach_map_letA_smul_comm, smul_smul]

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LemGA0ConvVanish
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

section LemGA0

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGA0_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (R := Qp) (M := T.V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem lemGA0_one_root (l : ℕ) : ∃ j : ℕ, IsPrimitiveRoot (1 : LL) (l ^ j) := ⟨0, by simpa using IsPrimitiveRoot.one⟩

theorem lemGA0_cc_letπ (W : LocWach PD LL O v n) (i : ZMod n) :
    PowerSeries.constantCoeff (W.lev i 1 (letπ : LetA O n)) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 (lemGA0_one_root PD.p)
  have h := congrArg PowerSeries.constantCoeff hE
  simp only [map_add, map_one, hE0, one_mul] at h
  linear_combination h

theorem lemGA0_cc_π₀₁ (W : LocWach PD LL O v n) (hcard : W.DelF.card = PD.p - 1) (hp : 1 ≤ PD.p) :
    PowerSeries.constantCoeff W.π₀₁ = 0 := by
  unfold LocWach.π₀₁
  have h2 : ∀ δ, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = (0 : O) := fun δ => (W.γ₀_X δ).1
  simp only [map_add, map_sub, map_one, map_natCast, map_sum, h2, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one, hcard]
  push_cast [Nat.cast_sub hp]
  ring

theorem lemGA0_cc_π₀ (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 W.π₀) = 0 := by
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr h0
  have e : W.π₀ = (letπ : LetA O n) * (fun _ => g) := by
    funext j
    show W.π₀₁ = PowerSeries.X * g
    exact hg
  rw [e, map_mul, map_mul, lemGA0_cc_letπ, zero_mul]

theorem lemGA0_cc_qp (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W)) = (PD.p : LL) := by
  unfold Formalism.MainNotions.LiftingTheory.qp
  rw [map_add, map_natCast, map_add, lemGA0_cc_π₀ W i h0, map_natCast, zero_add]

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]

theorem lemGA0_cc_pk (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.pk W 1)) = (PD.p : LL) := by
  have e : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA (Formalism.MainNotions.LiftingTheory.qp W) := by
    unfold Formalism.MainNotions.LiftingTheory.pk; rw [pow_one]
  rw [e, C.lev_φ i 1 (lemGA0_one_root PD.p) (Formalism.MainNotions.LiftingTheory.qp W), one_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, lemGA0_cc_qp W (i - 1) h0]

theorem lemGA0_conv_vanish {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hf : PowerSeries.constantCoeff f ≠ 0) (hsupp : ∃ m : ℤ, ∀ k < m, d k = 0)
    (hneg : ∀ r : ℤ, r < 0 → ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) = 0) :
    ∀ r : ℤ, r < 0 → d r = 0 := by
  obtain ⟨m, hm⟩ := hsupp
  have key : ∀ t : ℕ, ∀ r : ℤ, r < m + t → r < 0 → d r = 0 := by
    intro t
    induction t with
    | zero => intro r hr _; exact hm r (by simpa using hr)
    | succ t ih =>
      intro r hr hr0
      by_cases hlt : r < m + t
      · exact ih r hlt hr0
      · have hs : ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) =
            PowerSeries.coeff 0 f • d (r - ((0 : ℕ) : ℤ)) := by
          apply finsum_eq_single _ 0
          intro j hj
          rw [ih (r - j) (by push_cast at hr; omega) (by omega), smul_zero]
        have h := hneg r hr0
        rw [hs, Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
        have h' := congrArg (fun z => (PowerSeries.constantCoeff f)⁻¹ • z) h
        simpa [inv_smul_smul₀ hf] using h'
  intro r hr
  by_cases h : r < m
  · exact hm r h
  · apply key (r - m + 1).toNat r _ hr
    rw [Int.toNat_of_nonneg (by omega)]
    omega

theorem lemGA0_conv_zero {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hd : ∀ r : ℤ, r < 0 → d r = 0) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (0 - j) = PowerSeries.constantCoeff f • d 0 := by
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [hd _ (by have : (0 : ℕ) < j := Nat.pos_of_ne_zero hj; omega), smul_zero]

theorem lemGA0_of_tools [NeZero n] (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (hT : Formalism.MainNotions.CrystallineLiftingInputs.THor W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    LemGA_0 W := by
  intro d T₁ T₂ F b S η m hS i hi y hy hyD la hla x hx hxD hxe
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hS.2.2.2.2.2.1
  have hcr : IsCrys PD T₂.ρ := by unfold Formalism.MainNotions.LiftingTheory.Sur at hsur; exact hsur.2.1
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
    have hpos : 0 < PD.p := by omega
    have : NeZero PD.p := ⟨hpos.ne'⟩
    exact (hζ.neZero').out

  have hfr : finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq, Module.finrank_self]
  obtain ⟨hcard, -, h9K⟩ := h9 T₂ hcr hA.2.1 hA.2.2
  rw [hfr, Nat.div_one] at hcard
  have h0 : PowerSeries.constantCoeff W.π₀₁ = 0 := lemGA0_cc_π₀₁ W hcard (by omega)
  obtain ⟨-, hmod⟩ := h9K hfr
  have hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, 0, by simpa using hy⟩, ?_⟩
    obtain ⟨x', hx', he⟩ := hmod.2 y ⟨hy, hyD.2⟩
    exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact he⟩

  have hk : (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la ∈ W.N T₂ := by
    rw [pow_zero, one_mul, ← hxe]
    exact Submodule.smul_mem _ _ hx
  have hTH := hT hA hp11 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η))
    (Or.inr ⟨rfl, rfl, rfl⟩) T₂ hcr (i - 2) y la hy hyI hla.1 1 ((PD.p - 1) * 1) 0
    (Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) hk (Or.inr ⟨rfl, rfl⟩)
  have hneg := hTH.1
  have h0v := hTH.2 0 (by omega)
  have hi2 : i - 2 + ((2 : ℕ) : ZMod n) = i := by rw [Nat.cast_ofNat, sub_add_cancel]
  have hsub : (⟨(Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la, hk⟩ : ↥(W.N T₂)) =
      (Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, pow_zero, one_mul]
    exact hxe.symm
  rw [hi2, hsub] at hneg h0v
  rw [Nat.cast_zero] at h0v

  have hsm : ∀ r : ℤ, W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) r =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) •
        W.levN T₂ i 1 ⟨x, hx⟩ (r - j) :=
    fun r => W.levN_smul T₂ i 1 _ _ r
  have hccb : PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) = (PD.p : LL) ^ b i := by
    rw [map_pow, map_pow, lemGA0_cc_qp W i h0]
  have hxneg : ∀ r : ℤ, r < 0 → W.levN T₂ i 1 ⟨x, hx⟩ r = 0 :=
    lemGA0_conv_vanish (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) (W.levN T₂ i 1 ⟨x, hx⟩)
      (by rw [hccb]; exact pow_ne_zero _ hp0) (W.levN_supp T₂ i 1 _)
      (fun r hr => by rw [← hsm r]; exact hneg r hr)
  have he : ((letE i : LetA O n) • (⟨x, hx⟩ : ↥(W.N T₂))) = ⟨x, hx⟩ := Subtype.ext hxD.1
  have hL : W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) 0 =
      (PD.p : LL) ^ b i • ιV PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨x, hx⟩) := by
    rw [hsm, lemGA0_conv_zero _ _ hxneg, hccb, C.levN_eq, ← C.cmp_eq T₂ hcr i, he]
  have hcch : PowerSeries.coeff 0 (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S))) =
      (PD.p : LL) ^ (b (i - 1) + S) := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, pow_zero, one_mul, map_pow, map_pow,
      lemGA0_cc_pk W C i h0]
  have hmain : (PD.p : LL) ^ b i • W.cmp T₂ ⟨x, hx⟩ =
      (PD.p : LL) ^ (b (i - 1) + S) • ((PD.p : LL) ^ lemG_sig PD.p (hpar n b S + η) •
        (φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) := by
    apply lemGA0_ιV_inj (PD := PD) T₂
    rw [map_smul, map_smul, map_smul, ← hL, h0v, hcch]
  rw [← inv_smul_smul₀ (pow_ne_zero (b i) hp0) (W.cmp T₂ ⟨x, hx⟩), hmain, smul_smul, smul_smul,
    zpow_sub₀ hp0, zpow_add₀ hp0, zpow_natCast, zpow_natCast, zpow_natCast]
  congr 1
  ring

end LemGA0

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_letS (c : ZMod n) (x : W.DD T) : x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  unfold letS
  rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem mem_DelS (x : W.DD T) : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold DelS
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_NcS (c : ZMod n) (x : W.DD T) :
    x ∈ NcS W T c ↔ x ∈ W.N T ∧ (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold NcS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS, mem_letS, and_assoc]

theorem mem_PiNS (π' : LetA O n) (k : ℕ) (x : W.DD T) :
    x ∈ PiNS W T π' k ↔ (∃ y ∈ W.N T, π' ^ k • y = x) ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold PiNS
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS]
  unfold Formalism.MainNotions.DeltaInvariantLattices.aN
  rw [Submodule.mem_map]
  rfl

theorem mem_LamPS (Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ LamPS W T Eπ h' c ↔ Eπ ^ h' • x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) ∧
      (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold LamPS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_comap,
    mem_DelS, mem_letS, and_assoc]
  rfl

theorem mem_InvS (π' Eπ : LetA O n) (h' k : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ InvS W T π' Eπ h' k c ↔ x ∈ LamPS W T Eπ h' c ∧ W.γD T W.gamK x - x ∈ PiNS W T π' k := by
  unfold InvS
  rw [Submodule.mem_inf, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]

theorem PiNS_le_N (π' : LetA O n) (k : ℕ) {x : W.DD T} (hx : x ∈ PiNS W T π' k) : x ∈ W.N T := by
  obtain ⟨⟨y, hy, rfl⟩, -⟩ := (mem_PiNS W T π' k x).1 hx
  exact (W.N T).smul_mem _ hy

theorem γD_letE (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]

theorem φD_letE (c : ZMod n) (x : W.DD T) :
    W.φD T ((letE (c - 1) : LetA O n) • x) = (letE c : LetA O n) • W.φD T x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, Formalism.MainNotions.LiftingTheory.wmap_φA_letE]

theorem map_letA_smul {T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x :=
  Formalism.MainNotions.LiftingTheory.wmap_map_smul W f a x

theorem map_comp_zero {T' T'' : LocLat G Qp LL O} (ι : LatHom T.L T'.L) (π : LatHom T'.L T''.L)
    (h0 : ∀ y, π.f (ι.f y) = 0) (x : W.DD T) : W.map π (W.map ι x) = 0 := by
  rw [← W.map_comp]
  have hext : ∀ g₁ g₂ : LatHom T.L T''.L, g₁.f = g₂.f → g₁ = g₂ := by
    rintro ⟨f1, _, _, _⟩ ⟨f2, _, _, _⟩ h
    cases h
    rfl
  have hg : latAdd (latComp π ι) (latComp π ι) = latComp π ι := by
    apply hext
    ext y
    simp [latAdd, latComp, h0]
  have := W.map_latAdd (latComp π ι) (latComp π ι) x
  rw [hg] at this
  exact left_eq_add.mp this

end Local

end Formalism.MainNotions.N.Ln34

end
end

