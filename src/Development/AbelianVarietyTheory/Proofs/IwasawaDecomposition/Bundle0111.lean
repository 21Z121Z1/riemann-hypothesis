import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubSelfDual
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.DetSD

variable {L : Type} [Field L] [NumberField L]

theorem exists_det_ge {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (w : HeightOneSpectrum (𝓞 L)) (k : L) (hk0 : k ≠ 0)
    (hk : k ∈ detSub M) :
    ∃ x : Fin N → Fin N → L, (∀ i, x i ∈ M) ∧ w.valuation L k ≤ w.valuation L (Matrix.of x).det := by
  by_contra hn
  push Not at hn
  have h0 : w.valuation L k ≠ 0 := by simpa using hk0
  have key : ∀ z ∈ detSub M, w.valuation L z < w.valuation L k := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨x, hx, rfl⟩ := hd
      exact hn x hx
    | zero => rw [map_zero]; exact zero_lt_iff.2 h0
    | add x y _ _ hx hy => exact Valuation.map_add_lt _ hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (w.valuation_le_one r)) hx
  exact lt_irrefl _ (key k hk)

theorem coord_le_one {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (w : HeightOneSpectrum (𝓞 L))
    (x : Fin N → Fin N → L) (hx : ∀ i, x i ∈ M) (hd : (Matrix.of x).det ≠ 0)
    (hmax : ∀ z ∈ detSub M, w.valuation L z ≤ w.valuation L (Matrix.of x).det) (m : Fin N → L) (hm : m ∈ M)
    (j : Fin N) : w.valuation L (Matrix.vecMul m (Matrix.of x)⁻¹ j) ≤ 1 := by
  have hu : IsUnit (Matrix.of x).det := IsUnit.mk0 _ hd
  have h1 := congrFun (Matrix.det_smul_inv_vecMul_eq_cramer_transpose (Matrix.of x) m hu) j
  rw [Matrix.cramer_transpose_apply] at h1
  have h2 : ((Matrix.of x).updateRow j m).det ∈ detSub M := by
    refine det_mem_detSub (Function.update x j m) fun i => ?_
    by_cases h : i = j
    · subst h; simpa using hm
    · simpa [Function.update_of_ne h] using hx i
  have h3 := hmax _ h2
  rw [← h1, Pi.smul_apply, smul_eq_mul, map_mul] at h3
  have h0 : 0 < w.valuation L (Matrix.of x).det := zero_lt_iff.2 (by simpa using hd)
  exact (mul_le_iff_le_one_right h0).1 h3

theorem exists_den_prime {V : Type} [AddCommGroup V] [Module (𝓞 L) V] {N : ℕ} (M : Submodule (𝓞 L) V) (hM : M.FG)
    (w : HeightOneSpectrum (𝓞 L)) (f : Fin N → V → L) (hadd : ∀ j x y, f j (x + y) = f j x + f j y)
    (hsm : ∀ j (r : 𝓞 L) x, ∃ r' : 𝓞 L, f j (r • x) = r' • f j x)
    (hf : ∀ j, ∀ m ∈ M, w.valuation L (f j m) ≤ 1) :
    ∃ s : 𝓞 L, s ∉ w.asIdeal ∧ ∀ j, ∀ m ∈ M, (s : L) * f j m ∈ (algebraMap (𝓞 L) L).range := by
  classical
  obtain ⟨t, rfl⟩ := hM
  have := w.isPrime
  choose n d h using fun p : Fin N × t => w.exists_primeCompl_mul_eq_of_integer (f p.1 p.2)
    (hf p.1 p.2 (Submodule.subset_span p.2.2))
  refine ⟨((∏ p, d p : w.asIdeal.primeCompl) : 𝓞 L), (∏ p, d p).2, fun j m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, (⟨x, hx⟩ : t)))]
    refine ⟨((∏ p ∈ Finset.univ.erase (j, (⟨x, hx⟩ : t)), d p : w.asIdeal.primeCompl) : 𝓞 L) * n (j, ⟨x, hx⟩), ?_⟩
    rw [map_mul, ← h]
    simp only [Submonoid.coe_mul]
    push_cast
    simp only [RingOfIntegers.coe_eq_algebraMap]
    ring
  | zero =>
    obtain ⟨r, hr⟩ := hsm j 0 0
    have h0 : f j 0 = 0 := by simpa using hadd j 0 0
    rw [h0, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [hadd, mul_add]; exact add_mem hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr⟩ := hsm j r x
    rw [hr, Algebra.smul_def, mul_left_comm]
    exact mul_mem ⟨r', rfl⟩ hx

variable [StarRing L]

theorem star_integer (r : 𝓞 L) : ∃ r' : 𝓞 L, (r' : L) = star (r : L) :=
  ⟨RingOfIntegers.mapRingEquiv (starRingAut : RingAut L) r, rfl⟩

theorem star_mul_integer {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L))
    (hM : ∀ y ∈ M, ∀ x ∈ M, stdH L N x y ∈ (algebraMap (𝓞 L) L).range) (a b : L) (ha : a ∈ detSub M)
    (hb : b ∈ detSub M) : star a * b ∈ (algebraMap (𝓞 L) L).range := by
  induction ha using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    induction hb using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨y, hy, rfl⟩ := hd
      have e : star (Matrix.of x).det * (Matrix.of y).det = (Matrix.of fun i j => stdH L N (x j) (y i)).det := by
        rw [← Matrix.det_conjTranspose, mul_comm, ← Matrix.det_mul]
        congr 1
        ext i j
        simp [Matrix.mul_apply, stdH, mul_comm]
      rw [e]
      exact Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hM _ (hy i) _ (hx j)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Algebra.smul_def, mul_left_comm]; exact mul_mem ⟨r, rfl⟩ hx
  | zero => simp
  | add x y _ _ hx hy => rw [star_add, add_mul]; exact add_mem hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr⟩ := star_integer r
    rw [Algebra.smul_def, star_mul', mul_assoc]
    exact mul_mem ⟨r', hr⟩ hx

theorem ordSub_add_eq_zero {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (hM : IsSDLat L N M)
    (w w' : HeightOneSpectrum (𝓞 L)) (hw : ∀ x : L, w'.valuation L (star x) = w.valuation L x) :
    ordSub w (detSub M) + ordSub w' (detSub M) = 0 := by
  obtain ⟨hfg, hsp, hsd⟩ := hM
  have hl := (ordSub_detSub_lattice L N M hfg hsp).2.1
  obtain ⟨⟨k, hk, ek⟩, hkl⟩ := hl w
  obtain ⟨⟨k', hk', ek'⟩, hkl'⟩ := hl w'
  have nz : ∀ (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ), v.valuation L (a : L) ≠ 0 := fun v a => by simp
  apply le_antisymm
  · obtain ⟨x, hx, hxk⟩ := exists_det_ge M w k k.ne_zero hk
    have hd : (Matrix.of x).det ≠ 0 := by
      intro h
      rw [h, map_zero] at hxk
      exact nz w k (le_zero_iff.1 hxk)
    have hmax : ∀ z ∈ detSub M, w.valuation L z ≤ w.valuation L k := by
      intro z hz
      by_cases h0 : z = 0
      · simp [h0]
      · have h1 := hkl ⟨Units.mk0 z h0, hz, rfl⟩
        rw [← ek] at h1
        exact (WithZero.log_le_log (nz w (Units.mk0 z h0)) (nz w k)).1 (neg_le_neg_iff.1 h1)
    have hdk : w.valuation L (Matrix.of x).det = w.valuation L k := le_antisymm (hmax _ (det_mem_detSub x hx)) hxk
    have hc := coord_le_one M w x hx hd (fun z hz => hdk ▸ hmax z hz)
    set Y : Matrix (Fin N) (Fin N) L := ((Matrix.of x)⁻¹).conjTranspose with hY
    have hf : ∀ j m, stdH L N m (Y j) = star (Matrix.vecMul m (Matrix.of x)⁻¹ j) := by
      intro j m
      simp [stdH, hY, Matrix.vecMul, dotProduct]
    obtain ⟨s, hs, hint⟩ := exists_den_prime M hfg w' (fun j m => stdH L N m (Y j))
      (fun j a b => by simp [stdH, add_mul, Finset.sum_add_distrib])
      (fun j r a => by
        obtain ⟨r', hr⟩ := star_integer r
        refine ⟨r', ?_⟩
        have hr' : algebraMap (𝓞 L) L r' = star (algebraMap (𝓞 L) L r) := hr
        simp [stdH, Algebra.smul_def, hr', Finset.mul_sum, mul_assoc])
      (fun j m hm => by
        show w'.valuation L (stdH L N m (Y j)) ≤ 1
        rw [hf, hw]; exact hc m hm j)
    have hsY : ∀ j, ((s : L) • Y) j ∈ M := fun j => (hsd _).2 fun m hm => by
      have := hint j m hm
      convert this using 1
      simp [stdH, Finset.mul_sum, mul_left_comm]
    have hmem : ((s : L) • Y).det ∈ detSub M := det_mem_detSub (fun j => ((s : L) • Y) j) hsY
    have hsv : w'.valuation L (s : L) = 1 :=
      le_antisymm (w'.valuation_le_one s) (not_lt.1 fun h => hs ((w'.valuation_lt_one_iff_mem s).1 h))
    have hval : w'.valuation L ((s : L) • Y).det = (w.valuation L k)⁻¹ := by
      rw [Matrix.det_smul, map_mul, map_pow, hsv, one_pow, one_mul, hY, Matrix.det_conjTranspose, hw,
        Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hdk]
    have h0 : ((s : L) • Y).det ≠ 0 := by
      intro h
      rw [h, map_zero] at hval
      exact inv_ne_zero (nz w k) hval.symm
    have h1 := hkl' ⟨Units.mk0 _ h0, hmem, rfl⟩
    have h2 : ordF w' (Units.mk0 _ h0) = -ordF w k := by
      unfold ordF
      rw [Units.val_mk0, hval, WithZero.log_inv]
    omega
  · have h1 := star_mul_integer M (fun y hy => (hsd y).1 hy) k k' hk hk'
    have h2 := DetOrd.ordF_nonneg_of_isInteger w' (star k * k') h1
    rw [DetOrd.ordF_mul'] at h2
    have h3 : ordF w' (star k) = ordF w k := by
      unfold ordF
      rw [Units.coe_star, hw]
    omega

end GlobalTheory.Mem.Chr.DetSD

namespace GlobalTheory.Mem.Chr

open Classical in

theorem ordSub_detSub_selfDual : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; ∀ (M : SDLat H.E N) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' → ordSub w (detSub M.1) + ordSub w' (detSub M.1) = 0 := by
  intro R H N
  letI := H.cmStar
  intro M w w' h
  have hc : ConjPl H.conj.toRingEquiv w w' := (conjPl_main.2.1 R H w w').1 h
  refine DetSD.ordSub_add_eq_zero M.1 M.2 w w' fun x => ?_
  have := H.isCMField_hostE
  have e : star x = H.conj x :=
    H.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ H.φ₀ x).trans
      (H.conjE_apply H.φ₀ x).symm)
  rw [e]
  exact hc x

end GlobalTheory.Mem.Chr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpacesNormHasFrame
section
noncomputable section

namespace GlobalTheory.Mem.DiagSp

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain
open scoped TensorProduct

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem signSpace_cut_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N N' p q : ℕ)
    (hN : N = N') (hp : p ≤ N) (hq : N - p = q) :
    signSpace hstar N (cut N p) = stdSpace hstar N' (fun i => decide (p ≤ i.1)) p q := by
  subst hN hq
  rw [signSpace, card_cut_false N p hp, card_cut_true N p hp]
  rfl

theorem signSpace_false_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) :
    signSpace hstar N (fun _ => false) = stdSpace hstar N (fun _ => false) N 0 := by
  simp [signSpace]

def planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (a b : E) (i : Fin h) : Fin N → E :=
  Pi.single (⟨n + i, by omega⟩ : Fin N) a + Pi.single (⟨n + h + i, by omega⟩ : Fin N) b

theorem planeVec_planeVec (N n h p : ℕ) (hN : n + 2 * h ≤ N) (hp : p = n + h) (a b c d : E) (i j : Fin h) :
    diagForm N (cut N p) (planeVec N n h hN a b i) (planeVec N n h hN c d j) =
      if i = j then star a * c - star b * d else 0 := by
  subst hp
  have hi := i.isLt
  have hj := j.isLt
  have c1 : cut N (n + h) ⟨n + i, by omega⟩ = false := by simp [cut]
  have c2 : cut N (n + h) ⟨n + h + i, by omega⟩ = true := by simp [cut]
  simp only [planeVec, map_add, LinearMap.add_apply, diag_single_single, c1, c2]
  have e1 : ¬ (n + (i : ℕ) = n + h + j) := by omega
  have e2 : ¬ (n + h + (i : ℕ) = n + j) := by omega
  rw [if_neg e1, if_neg e2]
  by_cases hij : i = j
  · subst hij
    simp [sgn, sub_eq_add_neg]
  · have h' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have e3 : ¬ (n + (i : ℕ) = n + j) := by omega
    have e4 : ¬ (n + h + (i : ℕ) = n + h + j) := by omega
    rw [if_neg e3, if_neg e4, if_neg hij]
    simp

theorem ext_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (x : Fin n → E) (a b : E)
    (i : Fin h) : diagForm N neg (extTo n N x) (planeVec N n h hN a b i) = 0 := by
  rw [planeVec, map_add, diag_ext_single, diag_ext_single, add_zero]
  · simp only; omega
  · simp only; omega

theorem single_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (l : Fin N)
    (hl : n + 2 * h ≤ l) (c a b : E) (i : Fin h) :
    diagForm N neg (Pi.single l c) (planeVec N n h hN a b i) = 0 := by
  have hi := i.isLt
  rw [planeVec, map_add, diag_single_single, diag_single_single, if_neg, if_neg, add_zero]
  · simp only; omega
  · simp only; omega

end General

section Main

variable (R : Ranks)

theorem rankY_eq_N_add (j : ℕ) (hj : j < R.m) : R.rankY j = R.N j + (R.m - 1 - j) := by
  simp only [Ranks.rankY, Ranks.r, Ranks.N, mul_add]
  omega

theorem pY_eq_N_add (j : ℕ) (hj : j < R.m) : pY R j = R.N j + (R.m - 1 - j) / 2 := by
  have := rankY_eq_N_add R j hj
  simp only [pY]
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)

include hpz in
theorem top_line_norm :
    diagForm (R.N R.m) (fun _ => false)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz) = (T : E) := by
  refine (diag_single_single _ (fun _ => false) _ _ pz pz).trans ?_
  rw [if_pos rfl, ← hpz]
  simp [sgn]

def spacesNorm : Spaces R F E :=
  { spacesStd R cm T hT pz hpz (fun _ => false) with
    z := Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz
    z_anis := ne_of_eq_of_ne (top_line_norm R T pz hpz) (Nat.cast_ne_zero.2 hT.ne_zero)
    z_orth := fun x => diag_ext_single _ _ (fun _ => false) x _ pz le_rfl }

theorem spacesNorm_z_norm :
    ((spacesNorm R cm T hT pz hpz).X R.m).hT (spacesNorm R cm T hT pz hpz).z (spacesNorm R cm T hT pz hpz).z =
      ((spacesNorm R cm T hT pz hpz).T : E) :=
  top_line_norm R T pz hpz

theorem spacesNorm_hasFrame (j : ℕ) (hj : j < R.m) : HasHyperbolicAuxiliaryFrame (spacesNorm R cm T hT pz hpz) j := by
  have h1 := rankY_eq_N_add R j hj
  have h2 := pY_eq_N_add R j hj
  have hN : R.N j + 2 * ((R.m - 1 - j) / 2) ≤ R.rankY j := by omega
  refine ⟨planeVec _ _ _ hN (1 : E) 1, planeVec _ _ _ hN (1 / 2 : E) (-(1 / 2)),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans ?_,
    fun i x => ⟨ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i, ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i⟩,
    fun he => ?_⟩
  · split_ifs
    · rw [star_one]; norm_num
    · rfl
  · obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := R.m_even
    have hl : R.N j + 2 * ((R.m - 1 - j) / 2) < R.rankY j := by omega
    refine ⟨(Pi.single (⟨_, hl⟩ : Fin (R.rankY j)) pz : Fin (R.rankY j) → E), ?_,
      fun x => diag_ext_single _ _ (cut _ (pY R j)) x _ pz (Nat.le_add_right _ _),
      fun i => ⟨single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i,
        single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i⟩⟩
    refine (diag_single_single _ (cut _ (pY R j)) _ _ pz pz).trans ?_
    have c : cut (R.rankY j) (pY R j) ⟨_, hl⟩ = true := by
      simp only [cut, decide_eq_true_eq]; omega
    rw [if_pos rfl, c]
    change _ = -(T : E)
    rw [← hpz]
    simp [sgn]

theorem spacesNorm_coord :
    ∃ hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x),
      (∀ j, (spacesNorm R cm T hT pz hpz).X j = posSpace hstar (R.N j)) ∧
      (spacesNorm R cm T hT pz hpz).X' = posSpace hstar R.rankX' ∧
      (∀ j, (spacesNorm R cm T hT pz hpz).Y j =
        stdSpace hstar (R.rankY j) (fun i => decide ((sigYD R j).1 ≤ i.1)) (sigYD R j).1 (sigYD R j).2) ∧
      (∀ j, 1 ≤ j → j ≤ R.m → (spacesNorm R cm T hT pz hpz).W j =
        stdSpace hstar R.r (fun i => decide ((R.sigW j).1 ≤ i.1)) (R.sigW j).1 (R.sigW j).2) ∧
      ∀ j, (spacesNorm R cm T hT pz hpz).V j =
        stdSpace hstar R.nV (fun _ => (spacesNorm R cm T hT pz hpz).Vneg j)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then 0 else R.nV)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then R.nV else 0) := by
  refine ⟨star_isIntegral, fun _ => rfl, rfl, fun j => ?_, fun j h1 h2 => ?_, fun j => ?_⟩
  · exact signSpace_cut_eq _ _ _ _ _ rfl (Nat.sub_le _ _) (sub_pY R j)
  · have h : R.rankY 0 = R.k + R.m - 1 := by simp [Ranks.rankY, Ranks.r]
    refine signSpace_cut_eq _ (R.rankY 0) R.r (R.k + j - 1) (R.m - j) h ?_ ?_ <;> omega
  · exact signSpace_false_eq _ _

theorem spacesNorm_T : (spacesNorm R cm T hT pz hpz).T = T := rfl

theorem spacesNorm_Vneg (j : ℕ) : (spacesNorm R cm T hT pz hpz).Vneg j = false := rfl

theorem spacesNorm_Y_sig (j : ℕ) (τ : E →+* ℂ) : ((spacesNorm R cm T hT pz hpz).Y j).sig τ = sigYD R j :=
  spY_sig R j τ

end Main

end GlobalTheory.Mem.DiagSp

end
end

