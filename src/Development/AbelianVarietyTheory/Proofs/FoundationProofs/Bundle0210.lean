import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0206
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0207
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BadRowsShareBoundTwoPrimesStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.badRows_share_bound_two_primes : ∀ (g₁ g₂ : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (N m q d : ℕ) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂], 100000 ≤ N → PrimeOK g₁ q d → PrimeOK g₂ q d → ∀ (L₁ : ι₁ → Lev g₁ N) (L₂ : ι₂ → Lev g₂ N) (τ₁ : ι₁ → (ZMod g₁)[X] → GG g₁ N → ℂ) (τ₂ : ι₂ → (ZMod g₂)[X] → GG g₂ N → ℂ), (∀ v, IsSeries (τ₁ v)) → (∀ v, IsSeries (τ₂ v)) → ∀ (ch₁ : ι₁ → Fin m → (ZMod g₁)ˣ) (ch₂ : ι₂ → Fin m → (ZMod g₂)ˣ) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) (ep : ℝ), 0 ≤ ep → ep < 1 → CountAt ρ ep → (1 - (1 + ep) / (1 - ep) * (max 0 (badBound g₁ (Fintype.card ι₁) m N ((min q d : ℕ) : ℝ)) + max 0 (badBound g₂ (Fintype.card ι₂) m N ((min q d : ℕ) : ℝ)))) * (rk ρ (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e)) : ℝ) ≤ (rk ρ (conv (tens2 (eGood τ₁ ch₁) (eGood τ₂ ch₂)) (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e))) : ℝ) := by
  first | exact @GlobalTheory.BadShare.ShareThm.bad_share | exact GlobalTheory.BadShare.ShareThm.bad_share | (intros; apply GlobalTheory.BadShare.ShareThm.bad_share <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenfunctionalAllCharactersOfAtkinLehner
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lam_add' (B : ℕ) (c a b : ℕ → ℂ) : lam B c (a + b) = lam B c a + lam B c b := by
  simp only [lam, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem lam_smul' (B : ℕ) (c a : ℕ → ℂ) (z : ℂ) : lam B c (z • a) = z * lam B c a := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem slz_add' (k : ℕ) (δ : M2) (f g : ℍ → ℂ) : slz k δ (f + g) = slz k δ f + slz k δ g := by
  funext τ; simp only [slz, Pi.add_apply]; ring

theorem slz_smul' (k : ℕ) (δ : M2) (z : ℂ) (f : ℍ → ℂ) : slz k δ (z • f) = z • slz k δ f := by
  funext τ; simp only [slz, Pi.smul_apply, smul_eq_mul]; ring

theorem eigAll_of_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ)
    (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N →
    EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c → ∃ (B' : ℕ) (c' : ℕ → ℂ), EigAll k N l χ g (χ l * α) B' c' ∧
    ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' →
      qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a' := by
  intro k N l χ g α B c a₀ b₀ c₀ d₀ hdet hk hN hl hlN hE
  set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδ
  have hL : 0 < N * l := Nat.mul_pos hN hl.pos
  obtain ⟨hz1, hadd1, hsm1, -, -, -⟩ := mf_linear k (N * l) (ch χ)
  obtain ⟨hz2, hadd2, hsm2, -, -, -⟩ := mf_linear k (N * l) (ch χ⁻¹)

  have uniq : ∀ x y, MF k (N * l) (ch χ⁻¹) x → MF k (N * l) (ch χ⁻¹) y → qs x = qs y → x = y :=
    fun x y hx hy h => qs_injective x y hx.1 hy.1 h
  let S : Set (ℕ → ℂ) := {a | MF k (N * l) (ch χ) a}
  classical
  let φ : (ℕ → ℂ) → ℂ := fun a =>
    if h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) then lam B c h.choose else 0
  have hφ : ∀ a a', MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) → φ a = lam B c a' := by
    intro a a' h1 h2
    have h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) := ⟨a', h1, h2⟩
    simp only [φ, dif_pos h]
    rw [uniq _ _ h.choose_spec.1 h1 (h.choose_spec.2.trans h2.symm)]
  have hex : ∀ a, MF k (N * l) (ch χ) a → ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) :=
    fun a ha => GlobalTheory.T.atkinLehner_slash_isModularFormCoeffSeq k N l χ a a₀ b₀ c₀ d₀ hdet hk hN ha
  obtain ⟨B₀, hB₀⟩ := sturm_coef_zero k (N * l) N χ hL (dvd_mul_right N l)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.func_eq_lam S B₀ φ hz1
    (by
      intro a ha b hb
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨b', hb', eb⟩ := hex b hb
      obtain ⟨hab, hqab⟩ := hadd1 a b ha hb
      obtain ⟨hab', hqab'⟩ := hadd2 a' b' ha' hb'
      refine ⟨hab, ?_⟩
      rw [hφ a a' ha' ea, hφ b b' hb' eb, hφ (a + b) (a' + b') hab' (by rw [hqab', hqab, slz_add', ea, eb]),
        lam_add'])
    (by
      intro z a ha
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨hza, hqza⟩ := hsm1 z a ha
      obtain ⟨hza', hqza'⟩ := hsm2 z a' ha'
      refine ⟨hza, ?_⟩
      rw [hφ a a' ha' ea, hφ (z • a) (z • a') hza' (by rw [hqza', hqza, slz_smul', ea]), lam_smul'])
    (fun a ha h => hB₀ a ha h)
  obtain ⟨B', c', hagree, hkill⟩ := GlobalTheory.T.exists_lam_eq_and_vanishes_off_character k (N * l) N χ B₀ c₁ hL (dvd_mul_right N l)
  have key : ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) →
      lam B' c' a = lam B c a' := by
    intro a a' ha ha' e
    rw [hagree a ha, ← hc₁ a ha, hφ a a' ha' e]
  refine ⟨B', c', ⟨⟨?_, ?_⟩, hkill⟩, key⟩
  · intro a ha q hq hqNl
    obtain ⟨a', ha', ea⟩ := hex a ha
    have hqN : ¬ q ∣ N := fun h => hqNl (dvd_mul_of_dvd_left h l)
    obtain ⟨hT, -⟩ := GlobalTheory.T.atkinLehner_intertwines_hecke_operators k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hTa : MF k (N * l) (ch χ) (To k (ch χ q) q a) :=
      GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ a hk (dvd_mul_right N l) hq hqNl ha
    have hTa' : MF k (N * l) (ch χ⁻¹) (To k (ch χ⁻¹ q) q a') :=
      GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ⁻¹ a' hk (dvd_mul_right N l) hq hqNl ha'
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ q) _ hTa'
    rw [key _ _ hTa hs (by rw [hqs, hT q hq hqNl]), lam_smul', hE.T a' ha' q hq hqNl, key a a' ha ha' ea]
    have hunit : IsUnit ((q : ℕ) : ZMod N) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
    have h1 : χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = 1 := by
      rw [show χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = (χ * χ⁻¹) (q : ZMod N) by rw [MulChar.coeToFun_mul]; rfl,
        mul_inv_cancel, MulChar.one_apply hunit]
    simp only [ch, Int.cast_natCast]
    linear_combination (g q * lam B c a') * h1
  · intro a ha
    obtain ⟨a', ha', ea⟩ := hex a ha
    obtain ⟨-, hU⟩ := GlobalTheory.T.atkinLehner_intertwines_hecke_operators k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hper : ∀ (ε : DirichletCharacter ℂ N) (d : ℤ), ch ε (d + (N * l : ℕ)) = ch ε d := by
      intro ε d
      simp [ch]
    have hUa := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ) a hk hl (dvd_mul_left l N) (hper χ) ha).1
    have hUa' := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ⁻¹) a' hk hl (dvd_mul_left l N) (hper χ⁻¹) ha').1
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ l) _ hUa'
    rw [key _ _ hUa hs (by rw [hqs, hU]), lam_smul', hE.U a' ha', key a a' ha ha' ea]
    simp only [ch, Int.cast_natCast]
    ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularFormStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_periodic_weights_isModularForm : ∀ (j L₁ L₂ : ℕ) (a b χ₁ χ₂ : ℤ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → a 0 = 0 → (∀ x, a (x + L₁) = a x) → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ x, a (x * d) = χ₁ d * a x) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c a b) := by
  first | exact @GlobalTheory.eis_periodic_weights | exact GlobalTheory.eis_periodic_weights | (intros; apply GlobalTheory.eis_periodic_weights <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteLevelApproxOfGeometricInvariantModPo
section
open GlobalTheory.K5

namespace GlobalTheory.K5.GeoLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isAlgZp_zeta (T : Tower p Ω) (n : ℕ) : IsAlgZp p (T.ζ n) := by
  refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) 1
  · simp [(T.prim n).pow_eq_one]

def ggens (T : Tower p Ω) (N : ℕ) : Set Ω :=
  Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x} ∪ T.qq '' Set.Iic N

theorem ggens_mono (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : ggens T m ⊆ ggens T n := by
  unfold ggens
  gcongr

theorem fixes_ggens (T : Tower p Ω) (N : ℕ) (g : Gal p Ω)
    (hg : g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N)) :
    ∀ a ∈ ggens T N, g a = a := by
  have hgeo : ∀ x : Ω, IsAlgZp p x → g x = x := (Subgroup.mem_inf.mp hg).1
  have hq : g (T.qq N) = T.qq N := (Subgroup.mem_inf.mp hg).2
  rintro a ((⟨r, rfl⟩ | ha) | ⟨i, hi, rfl⟩)
  · exact g.commutes r
  · exact hgeo a ha
  · have hi' : i + (N - i) = N := Nat.add_sub_cancel' hi
    rw [GlobalTheory.K5.FinLevel.qq_eq_pow T i (N - i), hi', map_pow, hq]

theorem exists_level_of_fixed (hClo : IsClo p Ω) (T : Tower p Ω) (y : Ω)
    (hy : ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h y = y) :
    ∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y := by
  haveI := GlobalTheory.K5.FinLevel.charZero_of_tower T
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (⋃ n, ggens T n)
  have hmemL : ∀ a ∈ ⋃ n, ggens T n, a ∈ L := fun a ha => IntermediateField.subset_adjoin ℚ _ ha
  have hO : ∀ r : O0 p, algebraMap (O0 p) Ω r ∈ L := fun r =>
    hmemL _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl ⟨r, rfl⟩)⟩)
  let φ : O0 p →+* L := (algebraMap (O0 p) Ω).codRestrict L hO
  have hφ : ∀ r, algebraMap L Ω (φ r) = algebraMap (O0 p) Ω r := fun r => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hClo.inj
    rw [← hφ a, ← hφ b, hab]
  haveI halg : Algebra.IsAlgebraic L Ω := by
    constructor
    intro z
    obtain ⟨P, hP0, hPz⟩ := hClo.alg.isAlgebraic z
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφinj).mpr hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hPz
    convert hPz using 2
    exact RingHom.ext hφ
  haveI : IsAlgClosure L Ω := ⟨hClo.clo, halg⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  have hyL : y ∈ L := by
    have : y ∈ Set.range (algebraMap L Ω) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro f
      let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => f.commutes (φ r))
      have hfix : ∀ a ∈ ⋃ n, ggens T n, g a = a := fun a ha => f.commutes ⟨a, hmemL a ha⟩
      have hg : g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n := by
        refine Subgroup.mem_inf.mpr ⟨fun x hx => hfix x (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr hx)⟩),
          Subgroup.mem_iInf.mpr fun n => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
        · exact hfix _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr (isAlgZp_zeta T n))⟩)
        · exact hfix _ (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩⟩)
      exact hy g hg
    obtain ⟨l, rfl⟩ := this
    exact l.2
  obtain ⟨S, hS, hyS⟩ := IntermediateField.exists_finset_of_mem_adjoin hyL
  have hex : ∀ t ∈ S, ∃ m, t ∈ ggens T m := fun t ht => Set.mem_iUnion.mp (hS ht)
  choose! m hm using hex
  refine ⟨S.sup m, fun g hg => ?_⟩
  have hSN : (S : Set Ω) ⊆ ggens T (S.sup m) := fun t ht =>
    ggens_mono T (Finset.le_sup (f := m) ht) (hm t ht)
  have hyN : y ∈ IntermediateField.adjoin ℚ (ggens T (S.sup m)) :=
    IntermediateField.adjoin.mono ℚ _ _ hSN hyS
  let gq : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun q => by simp)
  have hle : Algebra.adjoin ℚ (ggens T (S.sup m)) ≤ AlgHom.equalizer (gq : Ω →ₐ[ℚ] Ω) (AlgHom.id ℚ Ω) :=
    Algebra.adjoin_le fun a ha => fixes_ggens T _ g hg a ha
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hyN
  have hr' : g r = r := hle hr
  have hs' : g s = s := hle hs
  rw [map_div₀, hr', hs']

end GlobalTheory.K5.GeoLevel

theorem GlobalTheory.K5.geo_invariants_from_finite_level :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ x : Ω, IsInt p x →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (g x) x) →
  ∃ y : Ω, IsInt p y ∧ (∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) ∧
    Cong p k ((T.ζ j - 1) * x) y := by
  intro p _ hp2 Ω _ _ hClo T k j hj x hx hfix
  obtain ⟨y₀, E, hy₀, hEH, huniq, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hClo T (Ggeo p Ω ⊓ ⨅ n, Gn T n) inf_le_right {x} j hj
  have hgi : ∀ (g : Gal p Ω) (z : Ω), IsInt p z → IsInt p (g z) := fun g z hz =>
    hz.map (g : Ω →ₐ[O0 p] Ω)
  refine ⟨∑ g ∈ E, g (y₀ * x), ?_, ?_, ?_⟩
  · exact IsIntegral.sum _ fun g _ => hgi g _ (hy₀.mul hx)
  · exact GlobalTheory.K5.GeoLevel.exists_level_of_fixed hClo T _
      (GlobalTheory.K5.FinLevel.sum_fixed _ E y₀ x hEH huniq)
  · have hz : ∀ g ∈ E, ∃ z : Ω, IsInt p z ∧ g x - x = (p : Ω) ^ k * z :=
      fun g hg => hfix g (hEH g hg)
    choose! z hzi hzx using hz
    refine ⟨-∑ g ∈ E, g y₀ * z g, ?_, ?_⟩
    · exact (IsIntegral.sum _ fun g hg => (hgi g _ hy₀).mul (hzi g hg)).neg
    · rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_neg, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_mul]
      linear_combination (-(g y₀)) * hzx g hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsCrisPOfIsCrisDR
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.FundSeq

def OntoAt (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ ι : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l ι →
    (∀ u : Per.Bcris l, ∃ x : Per.Bcris l, ι x ∈ Per.FilD l 0 ∧ x - Per.φB l x = u) ∧
    (∀ w : Per.BdR l, ∃ b : Per.Bcris l, Per.φB l b = b ∧ ι b - w ∈ Per.FilD l 0)

theorem pair_onto {B D : Type} [AddCommGroup B] [AddCommGroup D] (φ : B →+ B) (ι : B →+ D) (F : Set D)
    (h1 : ∀ u, ∃ x, x - φ x = u) (h2 : ∀ w, ∃ b, φ b = b ∧ ι b - w ∈ F) (u : B) (w : D) :
    ∃ x y, y ∈ F ∧ x - φ x = u ∧ ι x - y = w := by
  obtain ⟨x0, hx0⟩ := h1 u
  obtain ⟨b, hb, hF⟩ := h2 (w - ι x0)
  refine ⟨x0 + b, _, hF, ?_, ?_⟩
  · rw [map_add, hb, ← hx0]; abel
  · rw [map_add]; abel

variable {l : ℕ} [Fact l.Prime]

theorem exists_restrict_aCris_bdRPlus {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) :
    ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j ∧ ∀ x : Per.Acris l,
      ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x) := by
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.CrisIncl.exists_restrict l ι h
  exact ⟨j, ⟨h2, h3⟩, h1⟩

theorem eq_core_of_isCrisDR {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) (C : Core l) :
    ι = C.ι := by
  obtain ⟨j, hj, hι⟩ := exists_restrict_aCris_bdRPlus h
  have e : j = C.j := (crisP_unique_equivariant l C.j C.j_cris).1 j hj
  refine GlobalTheory.RingIface.bcris_ext l fun x => ?_
  rw [hι, C.ι_j, e]

theorem ontoAt_of_core (C : Core l) (h1 : C.OneSubPhiOnto) (h2 : C.FundOnto) : OntoAt l := by
  intro ι hι
  rw [eq_core_of_isCrisDR hι C]
  refine ⟨fun u => ?_, h2⟩
  obtain ⟨x, y, hy, hx, hxy⟩ := pair_onto (Per.φB l).toAddMonoidHom C.ι.toAddMonoidHom
    (Per.FilD l 0 : Set (Per.BdR l)) h1 h2 u 0
  exact ⟨x, (sub_eq_zero.1 hxy : C.ι x = y) ▸ hy, hx⟩

theorem pair_onto_of_tied {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (h : OntoAt l)
    (K : FinExt l) (u : P.R.B) (w : P.R.BdR) :
    ∃ (x : P.R.B) (y : P.R.BdR), y ∈ (P.PD K).Fil 0 ∧ x - (P.PD K).φ x = u ∧ (P.PD K).ι x - y = w := by
  obtain ⟨h1, h2⟩ := h _ T.incl
  have H := pair_onto (P.φB : P.R.B →+* P.R.B).toAddMonoidHom
    (P.ιB : P.R.B →+* P.R.BdR).toAddMonoidHom ((P.PD K).Fil 0 : Set P.R.BdR) (fun u => ?_) (fun w => ?_) u w
  · obtain ⟨x, y, hy, hx, hxy⟩ := H
    exact ⟨x, y, hy, by rw [P.PD_φ]; exact hx, by rw [P.PD_ι]; exact hxy⟩
  · obtain ⟨x, -, hx⟩ := h1 (T.eB u)
    obtain ⟨x, rfl⟩ := T.eB.surjective x
    refine ⟨x, T.eB.injective ?_⟩
    rw [← hx, map_sub, ← T.frob]
    rfl
  · obtain ⟨b, hb, hF⟩ := h2 (T.eD w)
    obtain ⟨b, rfl⟩ := T.eB.surjective b
    refine ⟨b, T.eB.injective ((T.frob b).trans hb), (T.fil K 0 _).2 ?_⟩
    have e : T.eB.symm.toRingHom (T.eB b) = b := T.eB.symm_apply_apply b
    rw [RingHom.comp_apply, e] at hF
    rw [map_sub]
    exact hF

theorem surjective_half_of_onto (h : ∀ (l : ℕ) [Fact l.Prime], OntoAt l) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.LocalSituation.adm1 D :=
  fun l _ K u w => pair_onto_of_tied (D.locT l) (h l) K u w

end GlobalTheory.FundSeq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMultisetSatakeEigenvalueEq
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun

open Polynomial in

theorem exists_multiset_esymm_eq (n : ℕ) (e : ℕ → ℂ) (h0 : e 0 = 1) (hn : e n ≠ 0) :
    ∃ A : Multiset ℂ, A.card = n ∧ (0 : ℂ) ∉ A ∧ ∀ j ≤ n, A.esymm j = e j := by
  set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), monomial k ((-1) ^ (n - k) * e (n - k)) with hp
  have hc : ∀ k, p.coeff k = if k ≤ n then (-1) ^ (n - k) * e (n - k) else 0 := fun k => by
    simp [hp, coeff_monomial]
  have hle : p.natDegree ≤ n := natDegree_le_iff_coeff_eq_zero.2 fun k hk => by rw [hc, if_neg (by omega)]
  have hcn : p.coeff n = 1 := by simp [hc, h0]
  have hd : p.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hcn])
  have hl : p.leadingCoeff = 1 := by rw [leadingCoeff, hd, hcn]
  have hr : p.roots.card = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  refine ⟨p.roots, hr.trans hd, fun hz => ?_, fun j hj => ?_⟩
  · have := isRoot_of_mem_roots hz
    rw [IsRoot, ← coeff_zero_eq_eval_zero, hc] at this
    simp [hn] at this
  · have := coeff_eq_esymm_roots_of_card hr (k := n - j) (by omega)
    rw [hc, if_pos (by omega), hl, hd, one_mul, Nat.sub_sub_self hj] at this
    exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) this).symm

theorem exists_satEig_eq : ∀ (q n : ℕ), q ≠ 0 → ∀ c : ℕ → ℂ, c 0 = 1 → c n ≠ 0 →
    ∃ B : Multiset ℂˣ, B.card = n ∧ ∀ j ≤ n, satEig q n B j = c j := by
  intro q n hq c h0 hn
  have hw : ∀ j : ℕ, (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) ≠ 0 := fun j h =>
    hq (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h).1)
  obtain ⟨A, hA, hz, he⟩ := exists_multiset_esymm_eq n
    (fun j => c j / (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) (by simp [h0]) (div_ne_zero hn (hw n))
  refine ⟨A.pmap (fun a (h : a ≠ 0) => Units.mk0 a h) (fun a ha h => hz (h ▸ ha)), by simp [hA], fun j hj => ?_⟩
  rw [satEig, Multiset.map_pmap]
  simp only [Units.val_mk0, Multiset.pmap_eq_map, Multiset.map_id']
  rw [he j hj]
  exact mul_div_cancel₀ _ (hw j)

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
section
noncomputable section

namespace GlobalTheory.LFun.SatCompare

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {f f' : G → ℂ} {x : V}

theorem hAct_orbit (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) (x : V) (g : G) :
    hAct K f (fun y => ρ y x) g = ρ g (heckeVec ρ K f x) := by
  refine Eq.symm (((ρ g).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_))
  simp

theorem orbit_mem_amf (hx : x ∈ fixed ρ K) :
    (fun y => ρ y x) ∈ AMF ℂ ⊥ K (Representation.trivial ℂ (⊥ : Subgroup G) V) := by
  intro γ g κ
  have : (γ : G) = 1 := Subgroup.mem_bot.1 γ.2
  simp [this, GlobalTheory.LGrp.mem_fixed.1 hx κ κ.2]

theorem heckeVec_mem_fixed (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K f x ∈ fixed ρ K := by
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
  have := Final.HeckeActMem G ⊥ K ℂ V _ hK f hf _ (orbit_mem_amf hx) 1 1 ⟨k, hk⟩
  simpa [hAct_orbit hK hf] using this

theorem heckeVec_conv (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K (conv K f f') x = heckeVec ρ K f (heckeVec ρ K f' x) := by
  have := congrFun (Final.HeckeActMul G ⊥ K ℂ V _ hK f hf f' hf' _ (orbit_mem_amf hx)) 1
  rw [funext (hAct_orbit hK hf' ρ x), hAct_orbit hK hf,
    hAct_orbit hK (Final.HeckeConvMem G K ℂ hK f hf f' hf')] at this
  simpa using this

theorem heckeVec_one (hK : IsCommensurated K) (hx : x ∈ fixed ρ K) : heckeVec ρ K (dosetInd ℂ K 1) x = x := by
  have := congrFun (Final.HeckeActOne G ⊥ K ℂ V _ _ (orbit_mem_amf hx)) 1
  rw [hAct_orbit hK (Final.DosetIndMem G K ℂ 1)] at this
  simpa using this

theorem heckeVec_add_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (x : V) :
    heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  unfold heckeVec
  rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)]
  exact finsum_congr fun c => by simp [add_smul]

theorem heckeVec_smul_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K (c • f) x = c • heckeVec ρ K f x := by
  unfold heckeVec
  rw [smul_finsum' c (finite_heckeVec hK hf ρ x)]
  exact finsum_congr fun c => by simp [mul_smul]

theorem heckeVec_zero_left (x : V) : heckeVec ρ K 0 x = 0 := by simp [heckeVec]

def heckeLin (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) : V →ₗ[ℂ] V where
  toFun := heckeVec ρ K f
  map_add' x y := by
    unfold heckeVec
    rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf ρ y)]
    exact finsum_congr fun c => by simp
  map_smul' c x := (map_heckeVec hK hf (c • LinearMap.id) (fun g y => by simp) x).symm

@[simp] theorem heckeLin_apply (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (x : V) :
    heckeLin hK hf ρ x = heckeVec ρ K f x := rfl

theorem heckeVec_smul (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K f (c • x) = c • heckeVec ρ K f x := (heckeLin hK hf ρ).map_smul c x

end GlobalTheory.LFun.SatCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnStripUnfoldedRankinIntegrandStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_strip_unfolded_rankin_integrand : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  first | exact @GlobalTheory.EisM.strip_integrable_rankin | exact GlobalTheory.EisM.strip_integrable_rankin | (intros; apply GlobalTheory.EisM.strip_integrable_rankin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowthStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_petersson_integrand_moderateGrowth : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (ρ : ℍ → ℝ) (F : ℍ → ℂ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → CF k L' (ch ε) a → AEStronglyMeasurable F → Mod F → Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k)) := by
  first | exact @GlobalTheory.EisM.integrable_pet_integrand | exact GlobalTheory.EisM.integrable_pet_integrand | (intros; apply GlobalTheory.EisM.integrable_pet_integrand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZeroStatement
section
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnitInTower_ne_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ), admitted c x → siegel T c x ≠ 0 := by
  first | exact @GlobalTheory.KZ.siegel_ne_zero | exact GlobalTheory.KZ.siegel_ne_zero | (intros; apply GlobalTheory.KZ.siegel_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVectorStatement
section
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnitInTower_sl_action_rowVector : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  first | exact @GlobalTheory.KZ.SiegelSL.sl_siegel | exact GlobalTheory.KZ.SiegelSL.sl_siegel | (intros; apply GlobalTheory.KZ.SiegelSL.sl_siegel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficientsStatement
section
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_unit_q_expansion_coefficients : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b : ℕ), 0 < M → a < M → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → Ω), GlobalTheory.QFam.HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => ε (A n)) ∧ (∀ n : ℕ, (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff (((k : ℚ) + n) / M) = A n) ∧ ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r = 0 := by
  first | exact @GlobalTheory.KExp.siegel_exp | exact GlobalTheory.KExp.siegel_exp | (intros; apply GlobalTheory.KExp.siegel_exp <;> assumption)
end

