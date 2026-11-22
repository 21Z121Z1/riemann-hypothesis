import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToOverSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0826
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3206
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3190
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3191
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectingStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField MonObj
open scoped NNReal TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatModel GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetHT.Bridge

section General

variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]

theorem exists_unit (hv : v.Integers O) {m : ℕ} (hm : m ≠ 0) {z : C} {a : Oˣ} (h : z ^ m = algebraMap O C a) :
    ∃ w : Oˣ, algebraMap O C w = z := by
  have h1 : v z = 1 := by
    have : v z ^ m = 1 := by rw [← map_pow, h]; exact hv.one_of_isUnit a.isUnit
    exact (pow_eq_one_iff_of_nonneg zero_le' hm).1 this
  obtain ⟨b, hb⟩ := hv.exists_of_le_one h1.le
  exact ⟨(hv.isUnit_of_one' (x := b) (hb ▸ h1)).unit, hb⟩

theorem units_root [IsAlgClosed C] (hv : v.Integers O) (n : ℕ) (hn : n ≠ 0) (a : Oˣ) : ∃ b : Oˣ, b ^ n = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Nat.pos_of_ne_zero hn)
  obtain ⟨b, hb⟩ := exists_unit hv hn hz
  exact ⟨b, Units.ext (hv.hom_inj (by rw [Units.val_pow_eq_pow_val, map_pow, hb, hz]))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {p : ℕ} [Fact p.Prime] [IsAlgClosed C] [CharZero C] {Λ : Type} [CommRing Λ] [StarRing Λ]
  {P : Point p v O Λ} {z : Sp O ⟶ X} {φ : P.G.left ⟶ t.G.left}

theorem exists_torsChar [IsLocallyNoetherian X] [IsDomain O] [IsFractionRing O C] [IsIntegrallyClosed O] [IsLocalRing O]
    (hφ : IsGrpPullback P.G t.G z φ) (n : ℕ) (s : P.T) :
    ∃ c : TorsChar t z (p ^ n), ∀ (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) (a : GlobalTheory.ChTor.Pts P.A.A),
      w ^ (p ^ n) = 1 → a.left ≫ P.gen ≫ φ = spMap (algebraMap O C) ≫ w.left →
        algebraMap O C (c.χ O w : O) = (GlobalTheory.HTLat.weil P.A (p ^ n) a (s.lev n) : C) := by
  classical
  have hq : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hk : 1 ≤ p ^ n := GlobalTheory.HTLat.one_le_ppow p n
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.WeilTorsChar.exists_mulEquiv_points z t.G P.G φ hφ (specO O O)
  obtain ⟨j, -, hj⟩ := P.exists_generic
  let ψ : (Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) →* GlobalTheory.ChTor.Pts P.A.A := j.comp Φ.symm.toMonoidHom
  have hψ : ∀ w, w ^ (p ^ n) = 1 → ψ w ^ (p ^ n) = 1 := fun w h => by rw [← map_pow, h, map_one]
  have hroot : ∀ w, w ^ (p ^ n) = 1 → (GlobalTheory.HTLat.weil P.A (p ^ n) (ψ w) (s.lev n) : C) ^ (p ^ n) =
      algebraMap O C (1 : Oˣ) := fun w h => by
    rw [← Units.val_pow_eq_pow_val, ← GlobalTheory.HTLat.weil_pow_left hk (hψ w h) (s.lev_pow n), hψ w h]
    simpa using GlobalTheory.HTLat.weil_pow_left hk (one_pow (p ^ n)) (s.lev_pow n) 0
  let χ : (Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) → Oˣ := fun w =>
    if h : w ^ (p ^ n) = 1 then (exists_unit P.integers hq (hroot w h)).choose else 1
  have hχ : ∀ w (h : w ^ (p ^ n) = 1),
      algebraMap O C (χ w : O) = (GlobalTheory.HTLat.weil P.A (p ^ n) (ψ w) (s.lev n) : C) := fun w h => by
    simp only [χ, dif_pos h]
    exact (exists_unit P.integers hq (hroot w h)).choose_spec
  have hmul : ∀ w w', w ^ (p ^ n) = 1 → w' ^ (p ^ n) = 1 → χ (w * w') = χ w * χ w' := by
    intro w w' h h'
    have h'' : (w * w') ^ (p ^ n) = 1 := by rw [mul_pow, h, h', _root_.one_mul]
    apply Units.ext
    apply P.integers.hom_inj
    rw [Units.val_mul, map_mul, hχ (w * w') h'', hχ w h, hχ w' h', map_mul,
      GlobalTheory.HTLat.weil_mul_left hk (hψ w h) (hψ w' h') (s.lev_pow n), Units.val_mul]
  haveI : CharZero O := (algebraMap O C).charZero
  haveI : IsAlgClosed (FractionRing O) := IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv
  obtain ⟨κ, hκ⟩ := GlobalTheory.TorsCharExt.exists_hom_extend (units_root P.integers) (p ^ n) χ hmul
  obtain ⟨c, hc⟩ := GlobalTheory.TorsCharExt.exists_char t z (p ^ n) hq κ
  refine ⟨c, fun w a hw ha => ?_⟩
  have hA : a = ψ w := by
    refine (hj (Φ.symm w) a).1 ?_
    apply hφ.1.hom_ext
    · rw [Category.assoc, ha, Category.assoc, ← hΦ, MulEquiv.apply_symm_apply]
    · rw [Category.assoc, Category.assoc, Over.w (Φ.symm w), P.gen_pull.1.w, ← Category.assoc, Over.w a]
      change 𝟙 _ ≫ spMap (algebraMap O C) = spMap (algebraMap O C) ≫ spMap (algebraMap O O)
      rw [Algebra.algebraMap_self, GlobalTheory.TorsCharExt.sp_id, Category.comp_id, Category.id_comp]
  rw [hc w hw, hκ w hw, hA]
  exact hχ w hw

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem dlogDvd_iff [IsLocallyNoetherian X] [IsDomain O] [IsFractionRing O C] [IsIntegrallyClosed O]
    [HenselianLocalRing O] [Algebra ℤ_[p] O] (hφ : IsGrpPullback P.G t.G z φ) (x : LieG P.Gt) (k : ℕ) :
    DlogDvd t z p k ((P.lieCmp x).1.left ≫ φ) ↔ ∀ s : P.T, (p : O) ^ k ∣ (P.al₀ s).1 x := by
  constructor
  · intro h s
    obtain ⟨c, hc⟩ := exists_torsChar hφ k s
    obtain ⟨g, hg⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : O) ^ k}) (TanPair.isTanAtG_lieG hφ (P.lieCmp x))
    have h1 := h k c g hg
    have h2 : (p : O ⧸ Ideal.span {(p : O) ^ k}) ^ k = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rwa [GlobalTheory.TorsCharDlog.snd_chi_eq t P z φ hφ k c s hc x g hg, h2, Ideal.span_singleton_zero, Ideal.mem_bot,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
  · intro h n c g hg
    obtain ⟨s, hs⟩ := GlobalTheory.CharWeil.exists_tate_gen t P z φ hφ n c
    obtain ⟨b, hb⟩ := h s
    rw [GlobalTheory.TorsCharDlog.snd_chi_eq t P z φ hφ n c s hs x g hg, hb, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

omit [IsAlgClosed C] [CharZero C] in

theorem lieTie_iff {Y : Scheme.{0}} (π : P.G.left ⟶ Y) (x : LieG P.Gt) (u : Sp (DualNumber C) ⟶ Y) :
    LieTie P (P.gen ≫ π) x u ↔ spMap (dualMap (algebraMap O C)) ≫ (P.lieCmp x).1.left ≫ π = u := by
  have key : ∀ u, LieTie P (P.gen ≫ π) x u → spMap (dualMap (algebraMap O C)) ≫ (P.lieCmp x).1.left ≫ π = u := by
    rintro u ⟨xG, u', h1, h2, h3⟩
    rw [← (P.eq_lieCmp_iff x _).2 h1, ← Category.assoc, ← h3, Category.assoc, h2]
  refine ⟨key u, fun h => ?_⟩
  obtain ⟨u', h'⟩ := exists_lieTie P (P.gen ≫ π) x
  rwa [← h, key u' h']

end General

theorem epsMul_comp {S : Type} [CommRing S] (a b : S) : spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul (a * b)) := by
  rw [spMap_spMap]
  congr 1
  ext s <;> simp [epsMul, mul_assoc]

theorem isCombAtG_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x u a w) (c : S) : IsCombAtG t x u (fun i => c * a i) (spMap (epsMul c) ≫ w) := by
  obtain ⟨y, hy, rfl⟩ := h
  let d : tEpsG x ⟶ tEpsG x := Over.homMk (spMap (epsMul c)) (by
    change spMap (epsMul c) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [← Category.assoc, spMap_spMap]
    congr 2
    ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
  let f : (tEpsG x ⟶ t.G) →* (tEpsG x ⟶ t.G) := MonoidHom.mk' (fun g => d ≫ g) fun g g' => MonObj.comp_mul d g g'
  refine ⟨fun i => f (y i), fun i => ?_, ?_⟩
  · change spMap (epsMul c) ≫ (y i).left = _
    rw [hy, ← Category.assoc, epsMul_comp]
  · have e : (List.ofFn fun i => f (y i)).prod = f (List.ofFn y).prod := by
      rw [map_list_prod, List.map_ofFn]; rfl
    rw [e]
    rfl

def latOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) {C : Type} [Field C] (S : Subring C) (p : ℕ) (x : Sp C ⟶ X) : Set (Sp (DualNumber C) ⟶ t.G.left) :=
  {v | ∃ xO : Sp ↥S ⟶ X, spMap S.subtype ≫ xO = x ∧ ∃ (m : ℕ) (vO : Sp (DualNumber ↥S) ⟶ t.G.left),
    IsTanAtG t xO vO ∧ spMap (dualMap S.subtype) ≫ vO = spMap (epsMul ((p : C) ^ m)) ≫ v ∧ DlogDvd t xO p m vO}

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

theorem mem_latHT_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ X) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left) :
    w ∈ latHT t p x ↔ ∃ xO : Sp 𝓞_ℂ_[p] ⟶ X, spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ xO = x ∧
      ∃ (m : ℕ) (vO : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left), IsTanAtG t xO vO ∧
        spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ vO = spMap (epsMul ((p : ℂ_[p]) ^ m)) ≫ w ∧ DlogDvd t xO p m vO := by
  have e : intO ℂ_[p] = (𝓞_ℂ_[p]).toSubring := Subring.ext fun a => (GlobalTheory.PadicComplexHost.mem_iff_norm p a).symm
  change w ∈ latOf t (intO ℂ_[p]) p x ↔ _
  rw [e]
  rfl

theorem bLie_lieComb {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (Q : PtP E p) :
    ∀ (m : ℕ) (a : Fin m → 𝓞_ℂ_[p]) (x : Fin m → LieG Q.Gt), Q.bLie (lieComb Q.Gt a x) = ∑ i, a i • Q.bLie (x i)
  | 0, _, _ => Q.bLie_zero.trans (Finset.sum_of_isEmpty _).symm
  | m + 1, a, x => by
    rw [lieComb_succ, Q.bLie_add, Q.bLie_scale, bLie_lieComb Q m, Fin.sum_univ_succ]
    rfl

theorem exists_pow_mul_integral {p : ℕ} [Fact p.Prime] {n : ℕ} (a : Fin n → ℂ_[p]) :
    ∃ (k : ℕ) (b : Fin n → 𝓞_ℂ_[p]), ∀ i, algebraMap 𝓞_ℂ_[p] ℂ_[p] (b i) = (p : ℂ_[p]) ^ k * a i := by
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ l, ‖(p : ℂ_[p]) ^ k * a l‖ ≤ 1 := by
    have (l : Fin n) : ∀ᶠ k : ℕ in Filter.atTop, ‖(p : ℂ_[p]) ^ k * a l‖ ≤ 1 := by
      have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).mul_const (a l)).norm
      rw [zero_mul, norm_zero] at this
      exact this.eventually_le_const zero_lt_one
    exact (Filter.eventually_all.2 this).exists
  exact ⟨k, fun i => ⟨_, (GlobalTheory.PadicComplexHost.mem_iff_norm p _).2 (hk i)⟩, fun _ => rfl⟩

theorem bridge : BridgeSt := by
  intro E _ _ _ H X _ _ t p hp _ Q yb π hπ n x u hu a w hw
  haveI : HenselianLocalRing 𝓞_ℂ_[p] := GlobalTheory.henselianLocalRing_of_valuationRing_of_isAlgClosed _ ℂ_[p]
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hψ := Q.gen_pull.comp hπ
  have hpow : ∀ k : ℕ, algebraMap 𝓞_ℂ_[p] ℂ_[p] ((p : 𝓞_ℂ_[p]) ^ k) = (p : ℂ_[p]) ^ k := fun k => by
    rw [map_pow, map_natCast]
  obtain ⟨k, b, hb⟩ := exists_pow_mul_integral a
  have h₀ : LieTie Q (Q.gen ≫ π) (lieComb Q.Gt b x) (spMap (epsMul ((p : ℂ_[p]) ^ k)) ≫ w) :=
    lieTie_lieComb E H X t p Q _ _ hψ n x u b _ hu (by simpa only [hb] using isCombAtG_scale hw _)
  have e₀ : Q.bLie (lieComb Q.Gt b x) = (p : ℂ_[p]) ^ k • ∑ j, a j • Q.bLie (x j) := by
    rw [bLie_lieComb, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, ← hb, algebraMap_smul]
  have hd : ∀ (m : ℕ) (y : LieG Q.Gt), Q.bLie y = (p : ℂ_[p]) ^ m • ∑ j, a j • Q.bLie (x j) →
      (DlogDvd t yb p m ((Q.lieCmp y).1.left ≫ π) ↔ ∑ j, a j • Q.bLie (x j) ∈ Q.latT) := fun m y hy => by
    rw [dlogDvd_iff hπ, Q.mem_latT_iff]
    refine forall_congr' fun s => exists_congr fun c => ?_
    rw [← Q.integers.hom_inj.eq_iff, ← Q.pairV_bLie, hy, map_smul, LinearMap.smul_apply, map_mul, hpow, smul_eq_mul,
      mul_right_inj' (pow_ne_zero m hp0), eq_comm]
  rw [mem_latHT_iff]
  constructor
  · rintro ⟨z, hz, m, vO, hO, hs, hD⟩
    haveI : IsDominant (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 Q.integers.hom_inj).le.trans bot_le)⟩
    obtain rfl : z = yb := ext_of_isDominant _ hz
    obtain ⟨y', rfl⟩ := TanPair.exists_lieG hπ hO
    obtain ⟨y, rfl⟩ := Q.lieCmp.surjective y'
    have h₁ := ((lieTie_iff π y _).2 hs).scale ((p : 𝓞_ℂ_[p]) ^ k)
    have h₂ := h₀.scale ((p : 𝓞_ℂ_[p]) ^ m)
    rw [← Category.assoc, epsMul_comp, hpow] at h₁ h₂
    rw [mul_comm] at h₂
    have e := congrArg Q.bLie (h₁.unique hψ.1 h₂)
    rw [Q.bLie_scale, Q.bLie_scale, e₀, ← algebraMap_smul ℂ_[p], ← algebraMap_smul ℂ_[p] ((p : 𝓞_ℂ_[p]) ^ m), hpow, hpow,
      smul_comm] at e
    exact (hd m y (smul_right_injective _ (pow_ne_zero k hp0) e)).1 hD
  · intro h
    exact ⟨yb, rfl, k, _, TanPair.isTanAtG_lieG hπ (Q.lieCmp _), (lieTie_iff π _ _).1 h₀, (hd k _ e₀).2 h⟩

end GlobalTheory.DetHT.Bridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBounded
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem continuous_val_mul_conj (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p)
    (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField) (hf : f ∈ P.H a b) (g : X.functionField) (hg : g ∈ P.H a b) :
    Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set i := pick (P.L.φ σ).isLB y₀
  set j := pick (P.A.φ σ).isLB y₀
  have hi : y₀ ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ y₀
  have hj : y₀ ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ y₀
  have hW : IsOpen (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have hWn := hW.mem_nhds ⟨hi, hj⟩
  have hrf : ContinuousAt (fun y : CxPts p σ => ratVal (P.loc a b f i j) y) y₀ :=
    (GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P a b σ f hf i j).1.continuousAt hWn
  have hrg : ContinuousAt (fun y : CxPts p σ => ratVal (P.loc a b g i j) y) y₀ :=
    (GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P a b σ g hg i j).1.continuousAt hWn
  have hφ : ContinuousAt ((P.L.φ σ).φ i) y₀ := CInfAt.continuousAt (P.L.cInf σ i y₀ hi)
  have hψ : ContinuousAt ((P.A.φ σ).φ j) y₀ := CInfAt.continuousAt (P.A.cInf σ j y₀ hj)
  have he : ContinuousAt (fun y : CxPts p σ =>
      ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ)) y₀ :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuous_exp.continuousAt.comp
      (((continuousAt_const.mul hφ).add (continuousAt_const.mul hψ)).neg.div_const 2))
  have hF : ContinuousAt (fun y : CxPts p σ =>
      ratVal (P.loc a b f i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) *
        (starRingEnd ℂ) (ratVal (P.loc a b g i j) y *
          ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ))) y₀ :=
    (hrf.mul he).mul (Complex.continuous_conj.continuousAt.comp (hrg.mul he))
  refine hF.congr ?_
  filter_upwards [hWn] with y hy
  obtain ⟨θ, hθ, hv⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b σ y i j hy.1 hy.2
  have h1 : θ * (starRingEnd ℂ) θ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]; simp
  rw [hv f hf, hv g hg]
  generalize ratVal (P.loc a b f i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) = A
  generalize ratVal (P.loc a b g i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) = B
  rw [map_mul]
  linear_combination (-(A * (starRingEnd ℂ) B)) * h1

theorem nu_eq_sqrt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    P.nu a b σ y f = Real.sqrt ((val P a b σ y f * (starRingEnd ℂ) (val P a b σ y f)).re) := by
  rw [← norm_val, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem continuous_val_and_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ),
      (∀ (σ : k →+* ℂ), ∀ f ∈ P.H a b, ∀ g ∈ P.H a b,
        Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g)) ∧
      ∀ f ∈ P.H a b, (∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f) ∧
        ∃ C : ℝ, ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ C := by
  intro k _ X _ p D hX P a b
  refine ⟨fun σ f hf g hg => continuous_val_mul_conj k X p P a b σ f hf g hg, fun f hf => ?_⟩
  have hc : ∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f := fun σ => by
    simp_rw [nu_eq_sqrt]
    exact Real.continuous_sqrt.comp (Complex.continuous_re.comp (continuous_val_mul_conj k X p P a b σ f hf f hf))
  refine ⟨hc, ?_⟩
  have hb : ∀ σ : k →+* ℂ, ∃ C : ℝ, ∀ y : CxPts p σ, P.nu a b σ y f ≤ C := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨C, hC⟩ := (isCompact_range (hc σ)).bddAbove
    exact ⟨C, fun y => hC ⟨y, rfl⟩⟩
  choose C hC using hb
  haveI := hX.finite_emb
  obtain ⟨M, hM⟩ := (Set.finite_range C).bddAbove
  exact ⟨M, fun σ y => (hC σ y).trans (hM ⟨σ, rfl⟩)⟩

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimAddDualCotangentDimLeHeight
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.PDivGroup.CotDim in

theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] (hp : (p : k) = 0) (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hp
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((relFrob hp Γ.dual).app 1)
  have haD : p ^ Module.finrank k (Cot k (Γ.dual.A 1)) ≤
      Module.finrank k (Γ.dual.A 1 ⧸ kerIdeal ((relFrob hp Γ.dual).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.dual.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ.dual 1))

  have hker : LinearMap.ker ((verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k := fun a ha => by
    have h1 := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h1
    rw [Submodule.restrictScalars_mem,
      ← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP (kerIdeal ((relFrob hp Γ).app 1))]
    exact h1
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have haA : p ^ Module.finrank k (Cot k (Γ.A 1)) ≤
      Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ 1))
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((relFrob hp Γ.dual).app 1 :
        (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  have key : p ^ (Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1))) ≤
      p ^ Γ.height := by
    rw [pow_add, mul_comm, ← hdimD, hord]
    exact Nat.mul_le_mul haD (haA.trans hrD)
  exact (Nat.pow_le_pow_iff_right hp2).1 key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotent
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem coeff_single_one_mul {σ R : Type} [CommRing R] [DecidableEq σ] (i : σ) (f g : MvPowerSeries σ R) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g + coeff (Finsupp.single i 1) f * constantCoeff g := by
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  rw [show (Finset.HasAntidiagonal.antidiagonal (1 : ℕ) : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} by decide]
  rw [Finset.sum_pair (by simp)]
  simp only [Function.Embedding.coe_prodMap, Prod.map_apply, Function.Embedding.coeFn_mk,
    Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply]

theorem counit_dUnit_evA : ∀ (k : Type) [CommRing k] (d : ℕ) (A : Type) [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)), (∀ i, Coalgebra.counit (R := k) (x i) = 0) → ∀ f : MvPowerSeries (Fin d) k, Coalgebra.counit (R := k) (evA k x hx f) = constantCoeff f ∧ dUnit k (evA k x hx f) = ∑ i, lin f i • dUnit k (x i) := by
  intro k _ d A _ _ x hx h0 f
  have hev : ∀ i, evA k x hx (X i) = x i := GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k (Fin d) A x hx
  let c0 : MvPowerSeries (Fin d) k →ₐ[k] k :=
    { (constantCoeff : MvPowerSeries (Fin d) k →+* k) with
      commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }
  have hc0 : ∀ g, c0 g = constantCoeff g := fun _ => rfl
  have h1 : (Bialgebra.counitAlgHom k A).comp (evA k x hx) = c0 :=
    GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d) k _ _ (fun i => by simp [hev, h0]) (fun i => by simp [hev, h0, hc0])
  refine ⟨(AlgHom.congr_fun h1 f).trans (hc0 f), ?_⟩
  letI : Module kᵐᵒᵖ (Cot k A) := Module.compHom _ ((RingHom.id k).fromOpposite mul_comm)
  haveI : IsCentralScalar k (Cot k A) := ⟨fun _ _ => rfl⟩
  let D : MvPowerSeries (Fin d) k →ₗ[k] Cot k A :=
    ∑ i, LinearMap.smulRight (coeff (Finsupp.single i 1)) (dUnit k (x i))
  have hD : ∀ g, D g = ∑ i, lin g i • dUnit k (x i) := fun g => by simp [D, lin]
  have hlin1 : ∀ i, lin (1 : MvPowerSeries (Fin d) k) i = 0 := fun i => by
    simp [lin, coeff_one]
  have hlinmul : ∀ (a b : MvPowerSeries (Fin d) k) i,
      lin (a * b) i = constantCoeff a * lin b i + lin a i * constantCoeff b := fun a b i =>
    coeff_single_one_mul i a b
  let L : MvPowerSeries (Fin d) k →ₗ[k] TrivSqZeroExt k (Cot k A) :=
    (TrivSqZeroExt.inlAlgHom k k (Cot k A)).toLinearMap ∘ₗ c0.toLinearMap +
        TrivSqZeroExt.inrHom k (Cot k A) ∘ₗ D
  have hLf : ∀ g, (L g).fst = constantCoeff g := fun g => by simp [L, hc0]
  have hLs : ∀ g, (L g).snd = ∑ i, lin g i • dUnit k (x i) := fun g => by simp [L, hD, TrivSqZeroExt.snd_sum]
  let ψ : MvPowerSeries (Fin d) k →ₐ[k] TrivSqZeroExt k (Cot k A) :=
    AlgHom.ofLinearMap L
      (by ext <;> simp [hLf, hLs, hlin1])
      (fun a b => by
        ext
        · simp [hLf]
        · rw [TrivSqZeroExt.snd_mul, hLs, hLs, hLs, hLf, hLf]
          simp only [hlinmul, add_smul, mul_smul, Finset.smul_sum, Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [op_smul_eq_smul, smul_comm])
  have hψf : ∀ g, (ψ g).snd = ∑ i, lin g i • dUnit k (x i) := hLs
  let φ : MvPowerSeries (Fin d) k →ₐ[k] TrivSqZeroExt k (Cot k A) :=
    (AugCot.toSqZero (Bialgebra.counitAlgHom k A) (LinearMap.id (M := Cot k A))).comp (evA k x hx)
  have hφf : ∀ g, (φ g).fst = Coalgebra.counit (R := k) (evA k x hx g) := fun g => by simp [φ]
  have hφs : ∀ g, (φ g).snd = dUnit k (evA k x hx g) := fun g => by simp [φ]
  have hlinX : ∀ i j, lin (X i : MvPowerSeries (Fin d) k) j = if j = i then 1 else 0 := fun i j => by
    simp [lin, coeff_X, Finsupp.single_left_inj one_ne_zero]
  have hφψ : φ = ψ := by
    refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d) _ _ _ (fun i => ⟨2, ?_⟩) (fun i => ?_)
    · ext
      · simp [pow_two, hφf, hev, h0]
      · simp [pow_two, TrivSqZeroExt.snd_mul, hφf, hev, h0]
    · ext
      · rw [hφf, hev, h0]; exact (constantCoeff_X i).symm.trans (hLf (X i)).symm
      · rw [hφs, hψf, hev]
        simp [hlinX]
  rw [← hφs, ← hψf, hφψ]

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalBundleModificationDescendsToGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalBundle_modification_descends_to_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∃ L : LB G.left, L.IsLB ∧ LBIso P'.L.L (L.pull β) := by
  first | exact @GlobalTheory.Mum.CubeDesc.cubicalBundle_descends | exact GlobalTheory.Mum.CubeDesc.cubicalBundle_descends | (intros; apply GlobalTheory.Mum.CubeDesc.cubicalBundle_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionSmoothDbarClosedStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((powAt G x k : Alt n)) S) v) ∧ dbarAt (fun x => (powAt G x k : Alt n)) v = 0 ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (transAt G G' x k) S) v) := by
  first | exact @GlobalTheory.ChernCalc.powAt_transAt_smooth | exact GlobalTheory.ChernCalc.powAt_transAt_smooth | (intros; apply GlobalTheory.ChernCalc.powAt_transAt_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernTransgressionFormEqPowerSumDiffStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_chernTransgressionForm_eq_power_sum_diff : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, dbarAt (fun x => transAt G G' x k) v = (powAt G v k : Alt n) - powAt G' v k := by
  first | exact @GlobalTheory.ChernCalc.dbarAt_transAt | exact GlobalTheory.ChernCalc.dbarAt_transAt | (intros; apply GlobalTheory.ChernCalc.dbarAt_transAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddedPartPointsOverClosedProjPointClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddedPart_points_over_closedProjPoint_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (H' : E.H.toScheme.Opens) (X : Scheme.{0}) (o : H'.toScheme ⟶ X) (g : X ⟶ PSpace R E.N), IsSeparated g → o ≫ g = H'.ι ≫ E.f → (∀ z : E.H.toScheme, π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ H') → ∀ w : PSpace R E.N, PSpace.str R E.N w = closedPoint R → ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' {w} = Set.range o ∩ g ⁻¹' {w} := by
  first | exact @GlobalTheory.Mum.FibClosed.range_inter_fibre_closed | exact GlobalTheory.Mum.FibClosed.range_inter_fibre_closed | (intros; apply GlobalTheory.Mum.FibClosed.range_inter_fibre_closed <;> assumption)
end

