import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaQuotientCharMulInvEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.TwistRowType

variable {E : Type} [Field E] [NumberField E]

def intSub (P : HeightOneSpectrum (𝓞 E)) : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := by simpa using IntAt.coe P 1
  add_mem' := IntAt.add
  zero_mem' := by simpa using IntAt.coe P 0
  neg_mem' := fun {a} ha => by
    have h := IntAt.mul (IntAt.coe P (-1)) ha
    simpa using h

def redHom (P : HeightOneSpectrum (𝓞 E)) : intSub P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := by simpa using reduction_coe P 1
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := by simpa using reduction_coe P 0
  map_add' a b := reduction_add a.2 b.2

theorem redHom_apply (P : HeightOneSpectrum (𝓞 E)) (a : intSub P) : redHom P a = redP P a.1 := rfl

theorem unitV_mul_eq_one {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {a b : E} (h : redP P a * redP P b = 1) : LocE.unitV ξ a * LocE.unitV ξ b = 1 := by
  have ha : IsUnit (redP P a) := isUnit_iff_exists_inv.2 ⟨_, h⟩
  have hb : IsUnit (redP P b) := isUnit_iff_exists_inv'.2 ⟨_, h⟩
  have hu : ha.unit * hb.unit = 1 := Units.ext (by simpa using h)
  simp only [LocE.unitV, dif_pos ha, dif_pos hb]
  rw [← Units.val_mul, ← map_mul, hu, map_one, Units.val_one]

variable [StarRing E]

theorem mem_stdAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

theorem mem_parL (P : HeightOneSpectrum (𝓞 E)) (q kj n : ℕ) (x : Sp E (n + 0)) :
    x ∈ LocE.parL P q kj n 0 ↔
      ∀ i : Fin (n + 0), IntAt P (((q : E) ^ (if kj ≤ i.1 ∧ i.1 < n then (1 : ℤ) else 0))⁻¹ * x i) := by
  rw [LocE.parL, LocE.sclLat, Submodule.mem_comap, mem_stdAt]
  exact Iff.rfl

theorem eN_mem (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt]
  intro j
  unfold Loc.eN
  split_ifs
  · simpa using IntAt.coe P 1
  · simpa using IntAt.coe P 0

theorem intAt_entry (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) (i j : ℕ) : IntAt P (Loc.atN (g (Loc.eN E N j)) i) := by
  have hg' : ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P := hg
  have hm : g (Loc.eN E N j) ∈ stdAt E N P := (hg' _).2 (eN_mem P N j)
  rw [mem_stdAt] at hm
  unfold Loc.atN
  split_ifs with h
  · exact hm _
  · simpa using IntAt.coe P 0

def blockD (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) : Matrix (Fin (n - kj)) (Fin (n - kj)) (intSub P) :=
  Matrix.of fun s t => ⟨Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1), intAt_entry P hg _ _⟩

theorem redP_det_block (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) :
    redP P (Matrix.det (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1))) =
      ((redHom P).mapMatrix (blockD P kj n hg)).det := by
  have h1 : (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1)) =
      (intSub P).subtype.mapMatrix (blockD P kj n hg) := by
    ext s t
    rfl
  rw [h1, ← RingHom.map_det, ← RingHom.map_det]
  rfl

theorem block_mul (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (kj n : ℕ)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ stabL E (n + 0) (stdAt E (n + 0) P))
    (hg' : g⁻¹ ∈ stabL E (n + 0) (stdAt E (n + 0) P)) (hp : g ∈ stabL E (n + 0) (LocE.parL P q kj n 0)) :
    (redHom P).mapMatrix (blockD P kj n hg * blockD P kj n hg') = 1 := by
  classical
  have hI1 : IntAt P (1 : E) := by simpa using IntAt.coe P 1
  have hI0 : IntAt P (0 : E) := by simpa using IntAt.coe P 0
  rcases le_or_gt kj n with hkn | hkn
  swap
  · ext s t
    exfalso
    have := s.2
    omega
  set h := g⁻¹ with hh

  have hent : ∀ (f : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) (i j : ℕ) (hi : i < n + 0) (hj : j < n + 0),
      Loc.atN (f (Loc.eN E (n + 0) j)) i = LinearMap.toMatrix' f.toLinearMap ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro f i j hi hj
    rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, Loc.atN, dif_pos hi]
    have he : Loc.eN E (n + 0) j = Pi.single (⟨j, hj⟩ : Fin (n + 0)) (1 : E) := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    rw [he]
  have hMM : LinearMap.toMatrix' g.toLinearMap * LinearMap.toMatrix' h.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro x
    exact g.apply_symm_apply x

  have hpar : ∀ x, g x ∈ LocE.parL P q kj n 0 ↔ x ∈ LocE.parL P q kj n 0 := hp
  have hq0E : (q : E) ≠ 0 := Nat.cast_ne_zero.mpr hq0
  have hqI : IntAt P (q : E) := by simpa using IntAt.coe P (q : 𝓞 E)
  have hredq : redP P (q : E) = 0 := by
    have hc := reduction_coe P (q : 𝓞 E)
    rw [map_natCast] at hc
    rw [hc, Ideal.Quotient.eq_zero_iff_mem]
    exact hq
  have hlow : ∀ u, u < kj → ∀ s, kj + s < n →
      redP P (Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s)) = 0 := by
    intro u hu s hs
    have hmem : Loc.eN E (n + 0) u ∈ LocE.parL P q kj n 0 := by
      rw [mem_parL]
      intro i
      unfold Loc.eN
      by_cases hi : i.1 = u
      · have hc : ¬ (kj ≤ i.1 ∧ i.1 < n) := by omega
        rw [if_pos hi, if_neg hc]
        simpa using hI1
      · rw [if_neg hi, mul_zero]
        exact hI0
    have h2 := (mem_parL P q kj n _).1 ((hpar _).2 hmem) ⟨kj + s, by omega⟩
    have hc : kj ≤ kj + s ∧ kj + s < n := ⟨by omega, hs⟩
    simp only [hc, and_self, ite_true, zpow_one] at h2
    have hval : Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s) =
        (q : E) * ((q : E)⁻¹ * g (Loc.eN E (n + 0) u) ⟨kj + s, by omega⟩) := by
      rw [Loc.atN, dif_pos (by omega : kj + s < n + 0), ← mul_assoc, mul_inv_cancel₀ hq0E, one_mul]
    rw [hval, reduction_mul hqI h2, hredq, zero_mul]

  have hid : ∀ s t : Fin (n - kj), ∑ u ∈ Finset.range (n + 0),
      Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s.1) * Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) u =
      if s = t then 1 else 0 := by
    intro s t
    have hs : kj + s.1 < n + 0 := by omega
    have ht : kj + t.1 < n + 0 := by omega
    have h3 := congrFun (congrFun hMM ⟨kj + s.1, hs⟩) ⟨kj + t.1, ht⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h3
    rw [← Fin.sum_univ_eq_sum_range]
    convert h3 using 1
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [hent g _ _ hs u.2, hent h _ _ u.2 ht]
    · simp [Fin.ext_iff]
  ext s t
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  set X := (blockD P kj n hg * blockD P kj n hg') s t with hXdef
  set Y : intSub P := ∑ u ∈ Finset.range kj,
    (⟨Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s.1), intAt_entry P hg _ _⟩ : intSub P) *
      ⟨Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) u, intAt_entry P hg' _ _⟩ with hYdef
  have hY : ((Y : intSub P) : E) = ∑ u ∈ Finset.range kj,
      Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s.1) * Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) u := by
    rw [hYdef]
    push_cast
    rfl
  have hXE : ((X : intSub P) : E) = ∑ x ∈ Finset.range (n - kj),
      Loc.atN (g (Loc.eN E (n + 0) (kj + x))) (kj + s.1) *
        Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) (kj + x) := by
    rw [hXdef, Matrix.mul_apply]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range (fun x => Loc.atN (g (Loc.eN E (n + 0) (kj + x))) (kj + s.1) *
        Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) (kj + x)) (n - kj)]
    rfl
  have hsum := hid s t
  rw [show Finset.range (n + 0) = Finset.range (kj + (n - kj)) from congrArg _ (by omega),
    Finset.sum_range_add] at hsum
  have hXY : X + Y = (1 : Matrix (Fin (n - kj)) (Fin (n - kj)) (intSub P)) s t := by
    apply Subtype.ext
    rw [Matrix.one_apply]
    show (X : E) + (Y : E) = _
    rw [hXE, hY, add_comm, hsum]
    split_ifs <;> rfl
  have hred : redHom P Y = 0 := by
    rw [hYdef, map_sum]
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [map_mul]
    simp only [redHom_apply]
    rw [hlow u (Finset.mem_range.1 hu) s.1 (by omega), zero_mul]
  have h4 := congrArg (redHom P) hXY
  rw [map_add, hred, add_zero] at h4
  rw [h4, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem lamQB_mul_inv : ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ), q ≠ 0 → (q : 𝓞 E) ∈ P.asIdeal → ∀ (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n : ℕ), ∀ g ∈ LocE.JQ P q kj n 0, LocE.lamQB ξ kj n g.toLinearMap * LocE.lamQB ξ kj n (g⁻¹).toLinearMap = 1 := by
  intro E K _ _ _ _ P q hq0 hq ξ kj n g hgJ
  rw [LocE.JQ, Subgroup.mem_inf] at hgJ
  obtain ⟨hg, hp⟩ := hgJ
  have hg' : g⁻¹ ∈ stabL E (n + 0) (stdAt E (n + 0) P) := Subgroup.inv_mem _ hg
  rw [LocE.lamQB, LocE.lamQB, ← mul_inv, unitV_mul_eq_one, inv_one]
  rw [redP_det_block P kj n hg, redP_det_block P kj n hg', ← Matrix.det_mul, ← RingHom.map_mul,
    block_mul P q hq0 hq kj n hg hg' hp, Matrix.det_one]

end GlobalTheory.TwistRowType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCartanDoubleCosetOfLatticeBetweenUniformizer
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

namespace GlobalTheory.ElemCartan

section Dvr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {r : ℕ}

theorem coord_of_mem_std {x : Fin r → K} (hx : x ∈ (std O K r).1) (i : Fin r) :
    ∃ a : O, algebraMap O K a = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

end Dvr

section Adic

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem zpow_mem_iff {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (m : ℤ) :
    ϖ ^ m ∈ w.adicCompletionIntegers E ↔ 0 ≤ m := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_zpow₀, hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zero, Multiplicative.ofAdd_le,
    smul_eq_mul]
  omega

theorem ne_zero_of_unif {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  intro h
  rw [IsUnifV, h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem antitone_zero_one {n j : ℕ} (a : Fin n → ℤ) (ha : Antitone a)
    (h01 : ∀ i, a i = 0 ∨ a i = 1)
    (hS : (Finset.univ.filter fun i => a i = 1).card = j) (i : Fin n) :
    a i = 1 ↔ (i : ℕ) < j := by
  first
  | exact @_root_.GlobalTheory.ClosedSubgroupCriterion.main
  | exact _root_.GlobalTheory.ClosedSubgroupCriterion.main
  | (apply _root_.GlobalTheory.ClosedSubgroupCriterion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosedSubgroupCriterion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosedSubgroupCriterion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosedSubgroupCriterion.main ..)

end Adic

theorem mem_doubleCoset_of_subElem : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (j : ℕ), j ≤ n → ∀ (g : GL (Fin n) (w.adicCompletion E)), haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) → ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w), (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  intro E _ _ w n ϖ hϖ j _ g hg
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  obtain ⟨M₀, hM, hMg⟩ := hg
  set L := std (w.adicCompletionIntegers E) (w.adicCompletion E) n with hLdef
  set M : Lat (w.adicCompletionIntegers E) (w.adicCompletion E) n := M₀ with hMdef
  have hϖ0 := ne_zero_of_unif w hϖ
  have hϖO : ϖ ∈ Ov E w := by
    have := (zpow_mem_iff w hϖ 1).2 zero_le_one
    simpa using this
  obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g
  have hs₁ : glMap k₁⁻¹ L.1 = L.1 := (GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n k₁⁻¹).2 (inv_mem hk₁)
  have hs₂ : glMap k₂⁻¹ L.1 = L.1 := (GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n k₂⁻¹).2 (inv_mem hk₂)
  set D : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hDdef
  have hD : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = diagPow E w ϖ a := by
    rw [hDdef, Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

  have hDL : glMap D L.1 = (k₁⁻¹ • M).1 := by
    rw [smul_def, glLat_val, hMg, hDdef, glMap_mul, glMap_mul, hs₂]
  have hMD : k₁⁻¹ • M ∈ subElem j L := by
    have h := (smul_mem_subElem_iff k₁⁻¹ j M L).2 hM
    have hL : k₁⁻¹ • L = L := GlobalTheory.LatHecke.Lat.ext (by rw [smul_def, glLat_val, hs₁])
    rwa [hL] at h
  obtain ⟨⟨hle, hidx⟩, hmax⟩ := hMD
  rw [← hDL] at hle hidx hmax
  have hDe : ∀ (x : Fin n → w.adicCompletion E) (i : Fin n),
      Matrix.toLin' (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x i = ϖ ^ (a i) * x i := by
    intro x i
    rw [Matrix.toLin'_apply, hD, diagPow, Matrix.mulVec_diagonal]

  have hpos : ∀ i, 0 ≤ a i := by
    intro i
    have hmem : Matrix.toLin' (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Pi.basisFun (w.adicCompletion E) (Fin n) i) ∈ glMap D L.1 :=
      ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := coord_of_mem_std (hle hmem) i
    rw [hDe] at hc
    simp only [Pi.basisFun_apply, Pi.single_eq_same, mul_one] at hc
    rw [← zpow_mem_iff w hϖ, ← hc]
    exact c.2

  have hle1 : ∀ i, a i ≤ 1 := by
    intro i
    have hϖm : (⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) := by
      apply (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))))).2
      show Valued.v ϖ < 1
      rw [hϖ, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
      omega
    have hmem : (⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) • L.1 :=
      Submodule.smul_mem_smul hϖm (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨x, hx, hxe⟩ := hmax hmem
    obtain ⟨c, hc⟩ := coord_of_mem_std hx i
    have hxi := congrFun hxe i
    simp only [LinearMap.coe_restrictScalars] at hxi
    rw [hDe] at hxi
    have hval : (((⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i) i) = ϖ := by
      simp [Algebra.smul_def]
    rw [hval] at hxi
    have hx' : x i = ϖ ^ (1 - a i) := by
      rw [zpow_sub₀ hϖ0, zpow_one, eq_div_iff (zpow_ne_zero (a i) hϖ0), mul_comm]
      exact hxi
    rw [← sub_nonneg, ← zpow_mem_iff w hϖ, ← hx', ← hc]
    exact c.2
  have h01 : ∀ i, a i = 0 ∨ a i = 1 := fun i => by
    have := hpos i; have := hle1 i; omega

  set S : Finset (Fin n) := Finset.univ.filter fun i => a i = 1 with hSdef
  have hdiag : (fun i => ϖ ^ (a i)) = fun i => if i ∈ S then ϖ else 1 := by
    funext i
    rcases h01 i with h | h <;> simp [hSdef, h]
  have hD' : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal fun i => if i ∈ S then ϖ else 1 := by
    rw [hD, diagPow, hdiag]
  obtain ⟨M₂, ⟨⟨-, hidx₂⟩, -⟩, hM₂⟩ := GlobalTheory.T.glMap_diagUniformizer_elementarySublattice E w n ϖ hϖ S D hD'
  rw [hM₂] at hidx₂
  have hcard : S.card = j := by
    have h := hidx₂.symm.trans hidx
    exact Nat.pow_right_injective (two_le_qRes (O := w.adicCompletionIntegers E)) h
  have hkey := antitone_zero_one a ha h01 hcard
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [e]
  congr 2
  rw [diagPow, diagJ]
  congr 1
  funext i
  by_cases hi : (i : ℕ) < j
  · rw [if_pos hi, (hkey i).2 hi, zpow_one]
  · rw [if_neg hi]
    have : a i = 0 := (h01 i).resolve_right fun h => hi ((hkey i).1 h)
    rw [this, zpow_zero]

end GlobalTheory.ElemCartan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThickLetterWordHypothesesOfCommonConditions
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem setting_of_wordBase : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)), D.nd.l i ≠ 2 → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → RecS.ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd := by
  intro D L HW i r ρ π w hw Cx hG Wd hl hB _ft T₁ T₂ F h1 h2 hF
  obtain ⟨ht1c, ht1w, ht1l⟩ := hB.t1 T₁ h1
  obtain ⟨ht2c, ht2low⟩ := hB.t2 T₂ h2
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨ht1c, ht2c, hF⟩, hB.small.1.2.2.2.2.2, ?_, fun a => ht2low _ft a, ?_, ht1l⟩
  · intro x y hxy
    have hv : ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 x : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) =
        ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 y : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) := by rw [hxy]
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.1, show y.1 ∈ Loc.K0 (D.nbr i w hw).Kw from ⟨y.2, hB.unram y.2⟩⟩, Subtype.ext rfl⟩
  · exact (HW _).W_s _ 1 _ hG
  · rw [(D.loc _).PD_p]; exact hl
  · intro a
    have hw' := ht1w a
    have e : Wd.win a = (if Wd.up a then
        Set.Icc (Wd.sz a : ℤ) ((Wd.sz a : ℤ) + Wd.S) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η
      else Set.Icc (-(Wd.sz a : ℤ) - Wd.S) (-(Wd.sz a : ℤ)) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η) := by
      unfold NWord.win
      cases h : Wd.up a <;> ext u <;> simp [abs_le]
    rw [← e]; exact hw'
  · intro a ha
    rcases hB.num.thick_or a with h | h
    · exact absurd h ha
    · exact h

end GlobalTheory.HTW.RecS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbedding
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_thick_iff : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → ∀ i, (pageWord L j ε τ φ).thick i ↔ Thick D.host (letter τ φ i) := by
  intro D L C j ε τ φ hR i
  obtain ⟨hlo, -⟩ := bHat_window L C hR
  obtain ⟨hwM, hwle⟩ := GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR
  have hR' := hR
  obtain ⟨hC, hw, ht, hwb, -, hb⟩ := hR'
  obtain ⟨c, hc⟩ := D.R.t_odd
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by nlinarith
  have hdiv : (D.R.t + 1) / 2 = c + 1 := by omega
  have hdivZ : ((D.R.t : ℤ) + 1) / 2 = (c : ℤ) + 1 := by omega
  have htc : (D.R.t : ℝ) = 2 * c + 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ L.sc.b by linarith)
  have hle := Nat.le_ceil L.sc.b
  have hsub : c + 1 ≤ ⌈L.sc.b⌉₊ := by
    have : ((c + 1 : ℕ) : ℝ) ≤ (⌈L.sc.b⌉₊ : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hbH : bHat L + (c + 1) = ⌈L.sc.b⌉₊ := by
    unfold bHat
    rw [hdiv]
    omega
  have hfl := Nat.lt_floor_add_one L.etaSz
  have hη : etaHat L = ⌊L.etaSz⌋₊ + D.R.t + 2 := rfl
  have hsz : ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ + ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = true) ∨
      ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ - ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = false) := by
    show szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _ ∨
      szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _
    unfold szT
    cases pos ε (letter τ φ i) <;> simp [hdivZ]
  have hbW : (pageWord L j ε τ φ).b = bHat L := rfl
  have hηW : (pageWord L j ε τ φ).η = etaHat L := rfl
  unfold WordData.thick
  rw [hbW, hηW, hη]
  generalize hE : ⌊(hcAt D (letter τ φ i)).e j⌋ = E at hsz
  constructor
  · rintro ⟨ha, hz⟩
    by_contra hnT
    have hEw : E ≤ (wMax D : ℤ) := hE ▸ hwle _ j hnT
    have hlt2 : ((wMax D + (c + 1) : ℕ) : ℝ) < (bHat L : ℝ) := by
      push_cast
      rw [htc] at hlo ht
      linarith
    have hlt3 : wMax D + (c + 1) < bHat L := by exact_mod_cast hlt2
    omega
  · intro hT
    obtain ⟨hA, hB⟩ := GlobalTheory.T.floor_size_bounds_at_thick_embedding L _ j hT
    rw [hE] at hA hB
    have hBE : ((⌈L.sc.b⌉₊ : ℤ)) ≤ E := by
      have : ((⌈L.sc.b⌉₊ : ℤ) : ℝ) < ((E + 1 : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_lt.mp this
      omega
    have hEB : E < (⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 := by
      have : ((E : ℤ) : ℝ) < (((⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp this
    omega

end GlobalTheory.HTW
end

