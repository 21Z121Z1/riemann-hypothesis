import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0126
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Formalism.JacquetSubsetSums.SeparationTR
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Formalism.GaloisCohomology.LocalTateDualityK

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersEqOnPrincipalCongruence
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

namespace KumUniq

theorem gamma_mem_of_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

end KumUniq

open KumUniq

theorem kum_near : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x χ' → Near χ χ' := by
  intro Ω _ _ ε X l _ n x χ χ' hK hK'
  obtain ⟨hH, hmul, hone, hdiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  obtain ⟨G1, G2, G3, -, G5⟩ := GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hχ⟩ := hK
  obtain ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hab'⟩, hχ'⟩ := hK'
  have hl : l.Prime := Fact.out
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨g, hfg⟩ := ((GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.1 f f').1 (hx.symm.trans hx')
  obtain ⟨p, q, hp, hq, hq0, hpq⟩ := X.an_mero (g : X.K)
  obtain ⟨M'', hM'', hlev⟩ := X.level (g : X.K)

  have nz : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → ∃ z ∈ Hs, u z ≠ 0 := by
    intro u hu hu0
    by_contra hc
    push_neg at hc
    exact hu0 (((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 hc).trans Filter.Germ.coe_zero)

  have unz : ∀ (h : X.Kˣ) (u : ℂ → ℂ) (v : Mero) (k : ℕ), k ≠ 0 → X.an (h : X.K) * (u : Mero) ^ k = v →
      DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → v ≠ 0 := by
    intro h u v k hk heq hu hu0 hv0
    have h0 : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero) := by
      have e : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = (u : Mero) ^ k := Filter.Germ.coe_pow u k
      rw [e]
      calc (u : Mero) ^ k = X.an (((h⁻¹ : X.Kˣ) : X.K) * (h : X.K)) * (u : Mero) ^ k := by simp
        _ = X.an ((h⁻¹ : X.Kˣ) : X.K) * (X.an (h : X.K) * (u : Mero) ^ k) := by rw [map_mul, mul_assoc]
        _ = 0 := by rw [heq, hv0, mul_zero]
        _ = _ := Filter.Germ.coe_zero.symm
    have h1 := (G1 _ _ (hu.pow k) (differentiableOn_const 0)).1 h0
    apply hu0
    refine ((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 fun z hz => ?_).trans Filter.Germ.coe_zero
    exact pow_eq_zero_iff hk |>.1 (h1 z hz)

  have nzmul : ∀ u v : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ v Hs → (∃ z ∈ Hs, u z ≠ 0) →
      (∃ z ∈ Hs, v z ≠ 0) → ∃ z ∈ Hs, u z * v z ≠ 0 := by
    rintro u v hu hv ⟨z1, hz1, h1⟩ ⟨z2, hz2, h2⟩
    by_contra hc
    push_neg at hc
    rcases G2 u v hu hv hc with h | h
    · exact h1 (h z1 hz1)
    · exact h2 (h z2 hz2)

  have hf : X.an (f : X.K) = X.an (f' : X.K) * X.an (g : X.K) ^ (l ^ n) := by
    rw [hfg, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  have key : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) =
      ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero) := by
    have e1 : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a : Mero) * b' * q) ^ (l ^ n) := by
      rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]; rfl
    have e2 : ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a' : Mero) * b * p) ^ (l ^ n) := by
      rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]; rfl
    rw [e1, e2, ← hpq]
    linear_combination (-((b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n))) * hab +
      ((b : Mero) ^ (l ^ n) * (b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hf +
      ((b : Mero) ^ (l ^ n) * (X.an (g : X.K)) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hab'
  have key' := (G1 _ _ (((ha.mul hb').mul hq).pow (l ^ n)) (((ha'.mul hb).mul hp).pow (l ^ n))).1 key
  obtain ⟨k, hk⟩ := G5 (l ^ n) (fun z => a z * b' z * q z) (fun z => a' z * b z * p z) hm
    ((ha.mul hb').mul hq) ((ha'.mul hb).mul hp) key'

  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (g : X.K) = (φ : Mero) :=
    Filter.Germ.inductionOn (X.an (g : X.K)) (p := fun F => ∃ φ : ℂ → ℂ, F = (φ : Mero)) fun φ => ⟨φ, rfl⟩
  have hmap : ∀ γ : SL(2, ℤ), Set.MapsTo (mob (ofSL γ)) Hs Hs := fun γ z hz => hH _ z hz
  have hpqδ : ∀ δ ∈ CongruenceSubgroup.Gamma M'', ∀ z ∈ Hs,
      p (mob (ofSL δ) z) * q z = p z * q (mob (ofSL δ) z) := by
    intro δ hδ
    have h1 : (φ : Mero) = ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := by
      rw [← hφ, ← X.an_sl (ofSL δ) _ φ hφ, hlev δ hδ]
    have h2 : ((fun z => φ z * q z : ℂ → ℂ) : Mero) = (p : Mero) := by
      rw [← hpq, hφ]; exact Filter.Germ.coe_mul φ q
    have h3 := G3 (ofSL δ) _ _ h2
    have e3 : ((fun z => φ (mob (ofSL δ) z) * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) :=
      Filter.Germ.coe_mul _ _
    have h2' : (φ : Mero) * (q : Mero) = (p : Mero) := by rw [← h2]; exact (Filter.Germ.coe_mul φ q).symm
    have h3' : ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := by rw [← e3]; exact h3
    have hpδ : DifferentiableOn ℂ (fun z => p (mob (ofSL δ) z)) Hs := hp.comp (hdiff _) (hmap δ)
    have hqδ : DifferentiableOn ℂ (fun z => q (mob (ofSL δ) z)) Hs := hq.comp (hdiff _) (hmap δ)
    refine (G1 (fun z => p (mob (ofSL δ) z) * q z) (fun z => p z * q (mob (ofSL δ) z))
      (hpδ.mul hq) (hp.mul hqδ)).1 ?_
    have e4 : ((fun z => p (mob (ofSL δ) z) * q z : ℂ → ℂ) : Mero) =
        ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * (q : Mero) := Filter.Germ.coe_mul _ _
    have e5 : ((fun z => p z * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        (p : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := Filter.Germ.coe_mul _ _
    rw [e4, e5]
    linear_combination (-((q : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero))) * h1 +
      ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * h2' + (-(q : Mero)) * h3'

  refine ⟨M * M' * M'', by positivity, fun δ hδ => ?_⟩
  have hδ1 : δ ∈ CongruenceSubgroup.Gamma M :=
    gamma_mem_of_dvd (Dvd.intro (M' * M'') (by ring)) hδ
  have hδ2 : δ ∈ CongruenceSubgroup.Gamma M' :=
    gamma_mem_of_dvd (Dvd.intro (M * M'') (by ring)) hδ
  have hδ3 : δ ∈ CongruenceSubgroup.Gamma M'' := gamma_mem_of_dvd (Dvd.intro_left (M * M') rfl) hδ
  set e1 := Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) with he1
  set e2 := Complex.exp (2 * Real.pi * Complex.I * ((χ' δ).val : ℂ) / ((l : ℂ) ^ n)) with he2
  set ζ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((l ^ n : ℕ) : ℂ)) with hζ
  have hP : ∀ z ∈ Hs, (e1 - e2) * (a z * a' z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) *
      p (mob (ofSL δ) z) * q z) = 0 := by
    intro z hz
    have hw := hH (ofSL δ) z hz
    have K1 := hχ δ hδ1 z hz
    have K2 := hχ' δ hδ2 z hz
    have K3 := hpqδ δ hδ3 z hz
    have Dz : a z * b' z * q z = ζ * (a' z * b z * p z) := hk z hz
    have Dw : a (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) =
        ζ * (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) := hk _ hw
    linear_combination (a' z * b z * p z) * Dw
      - (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) * Dz
      - (b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) * a' z * p z) * K1
      + e1 * (a z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * a' z) * K3
      + (a z * q z * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) * K2

  have nzδ : ∀ u : ℂ → ℂ, (∃ z ∈ Hs, u z ≠ 0) → ∃ z ∈ Hs, u (mob (ofSL δ) z) ≠ 0 := by
    rintro u ⟨z, hz, hu⟩
    refine ⟨mob (ofSL δ⁻¹) z, hH _ z hz, ?_⟩
    rwa [← hmul _ _ z hz, ← map_mul, mul_inv_cancel, map_one, hone]
  have dδ : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ (fun z => u (mob (ofSL δ) z)) Hs :=
    fun u hu => hu.comp (hdiff _) (hmap δ)
  have na : ∃ z ∈ Hs, a z ≠ 0 := nz a ha fun h0 => unz f b _ (l ^ n) hm.ne' hab hb hb0 (by rw [h0, zero_pow hm.ne'])
  have na' : ∃ z ∈ Hs, a' z ≠ 0 := nz a' ha' fun h0 => unz f' b' _ (l ^ n) hm.ne' hab' hb' hb0' (by rw [h0, zero_pow hm.ne'])
  have np : ∃ z ∈ Hs, p z ≠ 0 := nz p hp (unz g q _ 1 one_ne_zero (by rw [pow_one]; exact hpq) hq hq0)
  obtain ⟨z0, hz0, hne⟩ := nzmul _ _ ((((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')).mul (dδ p hp)) hq
    (nzmul _ _ (((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')) (dδ p hp)
      (nzmul _ _ ((ha.mul ha').mul (dδ b hb)) (dδ b' hb')
        (nzmul _ _ (ha.mul ha') (dδ b hb) (nzmul _ _ ha ha' na na') (nzδ b (nz b hb hb0)))
        (nzδ b' (nz b' hb' hb0'))) (nzδ p np)) (nz q hq hq0)
  have he : e1 = e2 := by
    rcases mul_eq_zero.1 (hP z0 hz0) with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne

  haveI : NeZero (l ^ n) := ⟨hm.ne'⟩
  have hprim := Complex.isPrimitiveRoot_exp (l ^ n) hm.ne'
  have ex : ∀ v : ℕ, Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ n)) =
      (Complex.exp (2 * Real.pi * Complex.I / ((l ^ n : ℕ) : ℂ))) ^ v := by
    intro v
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  apply ZMod.val_injective (l ^ n)
  exact hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [← ex, ← ex]; exact he)

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariant
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.KZ.LevelOneFrac

open Filter Topology Polynomial

theorem isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isConnected_Hs' : IsConnected Hs :=
  ⟨⟨Complex.I, by simp [Hs]⟩, (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected⟩

theorem eventually_nhdsNE {P : ℂ → Prop} (h : ∀ᶠ w in codiscreteWithin Hs, P w) {z : ℂ} (hz : z ∈ Hs) :
    ∀ᶠ w in 𝓝[≠] z, P w := by
  rw [Filter.Eventually, mem_codiscreteWithin] at h
  have h1 := Filter.disjoint_principal_right.1 (h z hz)
  have h2 : ∀ᶠ w in 𝓝[≠] z, w ∈ Hs := nhdsWithin_le_nhds (isOpen_Hs'.mem_nhds hz)
  filter_upwards [h1, h2] with w hw1 hw2
  by_contra hP
  exact hw1 ⟨hw2, hP⟩

theorem not_order_neg {h : ℂ → ℂ} {z : ℂ} (n : ℕ) (c : ℕ → ℂ → ℂ) (hc : ∀ i, ContinuousAt (c i) z)
    (hrel : ∀ᶠ w in 𝓝[≠] z, h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i = 0) :
    ¬ meromorphicOrderAt h z < 0 := by
  intro hneg
  have hinf := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  have hinv : Tendsto (fun w => (h w)⁻¹) (𝓝[≠] z) (𝓝 0) := tendsto_inv₀_cobounded.comp hinf
  have hne : ∀ᶠ w in 𝓝[≠] z, h w ≠ 0 := by
    have : ({0}ᶜ : Set ℂ) ∈ Bornology.cobounded ℂ := Bornology.isBounded_def.1 Bornology.isBounded_singleton
    exact hinf this
  have hF : Tendsto (fun w => 1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) (𝓝[≠] z)
      (𝓝 (1 + ∑ i ∈ Finset.range n, c i z * (0 : ℂ) ^ (n - i))) :=
    tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ =>
      ((hc i).tendsto.mono_left nhdsWithin_le_nhds).mul (hinv.pow _))
  have hlim : (1 + ∑ i ∈ Finset.range n, c i z * (0 : ℂ) ^ (n - i)) = 1 := by
    rw [add_eq_left]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : n - i ≠ 0 := by have := Finset.mem_range.1 hi; omega
    rw [zero_pow this, mul_zero]
  have hev : ∀ᶠ w in 𝓝[≠] z, (1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) = 0 := by
    filter_upwards [hrel, hne] with w hw hw0
    have hp : h w ^ n ≠ 0 := pow_ne_zero _ hw0
    have e : (1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) * h w ^ n =
        h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i := by
      rw [add_mul, one_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := (Finset.mem_range.1 hi).le
      have e2 : h w ^ n = h w ^ (n - i) * h w ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
      rw [e2, inv_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hw0)]
    rw [hw] at e
    exact (mul_eq_zero.1 e).resolve_right hp
  have h1 := tendsto_nhds_unique hF (tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm))
  rw [hlim] at h1
  exact one_ne_zero h1

theorem exists_differentiableOn {h : ℂ → ℂ} (hm : MeromorphicOn h Hs) (n : ℕ) (c : ℕ → ℂ → ℂ)
    (hc : ∀ i, DifferentiableOn ℂ (c i) Hs)
    (hrel : ∀ᶠ w in codiscreteWithin Hs, h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i = 0) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ h =ᶠ[codiscreteWithin Hs] φ := by
  refine ⟨toMeromorphicNFOn h Hs, ?_, toMeromorphicNFOn_eqOn_codiscrete hm⟩
  intro z hz
  have hNF : MeromorphicNFAt (toMeromorphicNFOn h Hs) z := meromorphicNFOn_toMeromorphicNFOn h Hs hz
  rcases meromorphicNFAt_iff_analyticAt_or.1 hNF with ha | ⟨-, hneg, -⟩
  · exact ha.differentiableAt.differentiableWithinAt
  · rw [meromorphicOrderAt_toMeromorphicNFOn hm hz] at hneg
    exact absurd hneg (not_order_neg n c
      (fun i => (hc i).continuousOn.continuousAt (isOpen_Hs'.mem_nhds hz)) (eventually_nhdsNE hrel hz))

end GlobalTheory.KZ.LevelOneFrac

namespace GlobalTheory.KZ.LevelOneFrac

open Filter Topology Polynomial

theorem germ_differentiableOn (G : Mero) (a b : ℂ → ℂ) (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (hb0 : (b : Mero) ≠ 0) (hab : G * (b : Mero) = (a : Mero)) (p : Mero[X]) (hp : p.Monic)
    (hc : ∀ i, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ p.coeff i = (φ : Mero)) (he : p.eval G = 0) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ G = (φ : Mero) := by
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs'
  have hB : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs'
  have hx : ∃ x ∈ Hs, b x ≠ 0 := by
    by_contra h
    push Not at h
    apply hb0
    rw [← Filter.Germ.coe_zero]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  obtain ⟨x, hxH, hx0⟩ := hx
  have hne : b ⁻¹' {0}ᶜ ∈ codiscreteWithin Hs :=
    hB.preimage_zero_mem_codiscreteWithin hx0 hxH isConnected_Hs'
  have h1 : ((b * b⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [← Filter.Germ.coe_one]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [hne] with z hz
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact mul_inv_cancel₀ hz
  have hG : G = ((a / b : ℂ → ℂ) : Mero) := by
    calc G = G * ((b * b⁻¹ : ℂ → ℂ) : Mero) := by rw [h1, mul_one]
      _ = (G * (b : Mero)) * ((b⁻¹ : ℂ → ℂ) : Mero) := by rw [Filter.Germ.coe_mul, mul_assoc]
      _ = ((a / b : ℂ → ℂ) : Mero) := by rw [hab, ← Filter.Germ.coe_mul, div_eq_mul_inv]
  have hM : MeromorphicOn (a / b) Hs := fun z hz => (hA z hz).meromorphicAt.div (hB z hz).meromorphicAt
  choose c hcd hce using hc
  set n := p.natDegree
  set g : ℂ → ℂ := a / b
  have key : ((fun w => g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i : ℂ → ℂ) : Mero) = 0 := by
    have e1 : ((fun w => g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i : ℂ → ℂ) : Mero) =
        Filter.Germ.coeRingHom _ (g ^ n + ∑ i ∈ Finset.range n, c i * g ^ i) := by
      congr 1
      ext w
      simp [Finset.sum_apply]
    rw [e1, map_add, map_pow, map_sum]
    simp_rw [map_mul, map_pow]
    change (g : Mero) ^ n + ∑ i ∈ Finset.range n, (c i : Mero) * (g : Mero) ^ i = 0
    rw [← hG]
    simp_rw [← hce]
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at he
    rw [add_comm]
    exact he
  have hrel : ∀ᶠ w in codiscreteWithin Hs, g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i = 0 := by
    have := Filter.Germ.coe_eq.1 (key.trans Filter.Germ.coe_zero.symm)
    filter_upwards [this] with w hw using hw
  obtain ⟨φ, hφ, hgφ⟩ := exists_differentiableOn hM n c hcd hrel
  exact ⟨φ, hφ, hG.trans (Filter.Germ.coe_eq.2 hgφ)⟩

end GlobalTheory.KZ.LevelOneFrac

namespace GlobalTheory.KZ.LevelOneFrac

open Filter Topology Polynomial

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem holRep (X : Tower Ω ε) (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) {r : X.K}
    (hr : r ∈ Algebra.adjoin Ω {X.jK}) : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an r = (φ : Mero) := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hj
  | algebraMap c => exact ⟨fun _ => ε c, differentiableOn_const _, X.an_c c⟩
  | add x y _ _ hx hy =>
    obtain ⟨φ, h1, h2⟩ := hx
    obtain ⟨ψ, h3, h4⟩ := hy
    exact ⟨φ + ψ, h1.add h3, by rw [map_add, h2, h4, Filter.Germ.coe_add]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨φ, h1, h2⟩ := hx
    obtain ⟨ψ, h3, h4⟩ := hy
    exact ⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩

theorem sl_eq_of_mem (X : Tower Ω ε) {r : X.K} (hr : r ∈ Algebra.adjoin Ω {X.jK}) (γ : SL(2, ℤ)) :
    X.sl (ofSL γ) r = r := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact X.j_inv γ
  | algebraMap c => exact (X.sl (ofSL γ)).commutes c
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem exists_denom (X : Tower Ω ε) {c : X.K} (hc : c ∈ IntermediateField.adjoin Ω {X.jK}) :
    ∃ d ∈ Algebra.adjoin Ω {X.jK}, d ≠ 0 ∧ d * c ∈ Algebra.adjoin Ω {X.jK} := by
  obtain ⟨r, hr, s, hs, rfl⟩ := (IntermediateField.mem_adjoin_iff_div (x := c)).1 hc
  by_cases h : s = 0
  · refine ⟨1, Subalgebra.one_mem _, one_ne_zero, ?_⟩
    rw [h, div_zero, mul_zero]
    exact Subalgebra.zero_mem _
  · refine ⟨s, hs, h, ?_⟩
    rwa [mul_div_cancel₀ r h]

theorem exists_denom_finset (X : Tower Ω ε) (s : Finset X.K) (hs : ∀ c ∈ s, c ∈ IntermediateField.adjoin Ω {X.jK}) :
    ∃ d ∈ Algebra.adjoin Ω {X.jK}, d ≠ 0 ∧ ∀ c ∈ s, d * c ∈ Algebra.adjoin Ω {X.jK} := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Subalgebra.one_mem _, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨d, hd, hd0, hds⟩ := ih (fun c hc => hs c (Finset.mem_insert_of_mem hc))
    obtain ⟨e, he, he0, hea⟩ := exists_denom X (hs a (Finset.mem_insert_self a s))
    refine ⟨e * d, Subalgebra.mul_mem _ he hd, mul_ne_zero he0 hd0, fun c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    · rw [mul_comm e d, mul_assoc]
      exact Subalgebra.mul_mem _ hd hea
    · rw [mul_assoc]
      exact Subalgebra.mul_mem _ he (hds c hc)

theorem isAlgebraic_adjoin (X : Tower Ω ε) (f : X.K) : IsAlgebraic (Algebra.adjoin Ω {X.jK}) f := by
  classical
  obtain ⟨p, hp0, hpf⟩ := X.alg_j f
  obtain ⟨d, hd, hd0, hds⟩ := exists_denom_finset X (p.support.image (fun i => (p.coeff i : X.K)))
    (by
      intro c hc
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
      exact (p.coeff i).2)
  let P : X.K[X] := C d * p.map (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K)
  have hlift : P ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {X.jK}) X.K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ p.support
    · refine ⟨⟨_, hds _ (Finset.mem_image_of_mem _ hn)⟩, ?_⟩
      simp [P, coeff_C_mul]
    · have h0 : p.coeff n = 0 := Polynomial.notMem_support_iff.1 hn
      refine ⟨0, ?_⟩
      simp [P, coeff_C_mul, h0]
  obtain ⟨q, hq⟩ := hlift
  rw [Polynomial.coe_mapRingHom] at hq
  refine ⟨q, ?_, ?_⟩
  · rintro rfl
    rw [Polynomial.map_zero] at hq
    have h2 := hq.symm
    simp only [P, mul_eq_zero, Polynomial.C_eq_zero, Polynomial.map_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact hd0 h2
    · exact hp0 h2
  · rw [aeval_def, eval₂_eq_eval_map, hq]
    simp only [P, eval_mul, eval_C, eval_map, ← aeval_def, hpf, mul_zero]

theorem mem_adjoin_of_sl_inv : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ f : X.K,
    (∀ γ : SL(2, ℤ), X.sl (ofSL γ) f = f) → f ∈ IntermediateField.adjoin Ω {X.jK} := by
  intro Ω _ _ _ ε X hj f hf
  obtain ⟨y, hy0, hyi⟩ := (isAlgebraic_adjoin X f).exists_integral_multiple
  set g : X.K := (y : X.K) * f with hgdef
  have hyf : y • f = g := rfl
  rw [hyf] at hyi
  have hginv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) g = g := fun γ => by
    rw [hgdef, map_mul, sl_eq_of_mem X y.2 γ, hf γ]
  obtain ⟨p, hpm, hpe⟩ := hyi
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero g
  obtain ⟨φ, hφ, hgφ⟩ := germ_differentiableOn (X.an g) a b ha hb hb0 hab
    (p.map (X.an.comp (algebraMap (Algebra.adjoin Ω {X.jK}) X.K))) (hpm.map _)
    (fun i => by rw [coeff_map]; exact holRep X hj (p.coeff i).2)
    (by rw [eval_map, ← Polynomial.hom_eval₂, hpe, map_zero])
  have hgR : g ∈ Algebra.adjoin Ω {X.jK} := GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε X ε.injective hj g hginv ⟨φ, hφ, hgφ⟩
  have hle := IntermediateField.algebra_adjoin_le_adjoin Ω ({X.jK} : Set X.K)
  have hyL : (y : X.K) ∈ IntermediateField.adjoin Ω {X.jK} := hle y.2
  have hgL : g ∈ IntermediateField.adjoin Ω {X.jK} := hle hgR
  have hy0' : (y : X.K) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hfe : f = g / y := by rw [hgdef, mul_div_cancel_left₀ _ hy0']
  rw [hfe]
  exact div_mem hgL hyL

end GlobalTheory.KZ.LevelOneFrac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PacketSumSignCastNeZero
section
open Finset

namespace GlobalTheory

lemma packetSum_vdm_eq_det {r : ℕ} (β : Fin r → ℂ) :
    Formalism.PacketSums.vdm β = (∏ i : Fin r, ∏ _j ∈ Ioi i, (-1 : ℂ)) * (Matrix.vandermonde β).det := by
  rw [Matrix.det_vandermonde, ← Finset.prod_mul_distrib]
  unfold Formalism.PacketSums.vdm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  have : Finset.univ.filter (fun j => i < j) = Ioi i := by ext; simp
  rw [this]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

lemma packetSum_vdm_perm {r : ℕ} (α : Fin r → ℂ) (σ : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.vdm (fun i => α (σ i)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * Formalism.PacketSums.vdm α := by
  rw [packetSum_vdm_eq_det, packetSum_vdm_eq_det]
  have : Matrix.vandermonde (fun i => α (σ i)) = (Matrix.vandermonde α).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde_apply]
  rw [this, Matrix.det_permute]
  ring

lemma packetSum_sign_cast_ne_zero {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma packetSum_numK_perm {r : ℕ} (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK]
    (μ : Fin r → ℤ) (α : Fin r → ℂ) (y : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) =
      ((Equiv.Perm.sign y : ℤ) : ℂ) * ∑ w : WK,
        ((Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) : ℤ) : ℂ) *
          ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
  unfold Formalism.PacketSums.numK
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hp : ∏ i, α (y⁻¹ i) ^ μ ((w : Equiv.Perm (Fin r))⁻¹ i) =
      ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
    rw [← Equiv.prod_comp y]
    simp [mul_inv_rev, Equiv.Perm.mul_apply]
  rw [hp, ← mul_assoc]
  congr 1
  have hs : Equiv.Perm.sign (w : Equiv.Perm (Fin r)) =
      Equiv.Perm.sign y * Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [hs]; push_cast; ring

theorem packetSum : Formalism.PacketSums.PacketSum := by
  intro r WK _ T hbij μ α _ _
  set f : Equiv.Perm (Fin r) → ℂ := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, α j ^ μ (σ⁻¹ j) with hf
  have hterm : ∀ y : Equiv.Perm (Fin r),
      Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α (y⁻¹ i)) =
        (∑ w : WK, f (y⁻¹ * (w : Equiv.Perm (Fin r)))) / Formalism.PacketSums.vdm α := by
    intro y
    rw [packetSum_numK_perm, packetSum_vdm_perm α y⁻¹, Equiv.Perm.sign_inv,
      mul_div_mul_left _ _ (packetSum_sign_cast_ne_zero y)]
  rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_coe_sort T]
  rw [← Fintype.sum_bijective _ hbij (fun p : WK × T => f ((p.2 : Equiv.Perm (Fin r))⁻¹ * p.1)) f
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntLengthEqOfCardQuotientEqCardSubmoduleStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_length_eq_of_card_quotient_eq : ∀ (l : ℕ) [Fact l.Prime] (X Y : Type) [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y] (N : ℕ → Submodule ℤ_[l] X) (P : ℕ → Submodule ℤ_[l] Y) (c : ℕ), Antitone N → (∀ x, (∀ r, x ∈ N r) → x = 0) → Monotone P → (∀ y, ∃ r, y ∈ P r) → (∀ r, c ≤ r → Finite (P r) ∧ Nat.card (X ⧸ N r) = Nat.card (P r)) → Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  first | exact @GlobalTheory.padicInt_length_eq_of_card_quotient_eq_card_submodule | exact GlobalTheory.padicInt_length_eq_of_card_quotient_eq_card_submodule | (intros; apply GlobalTheory.padicInt_length_eq_of_card_quotient_eq_card_submodule <;> assumption)
end

