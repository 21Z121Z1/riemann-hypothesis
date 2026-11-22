import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0067
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Dominated

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedVOfGeneratedMod
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenerationOfH1GenAmple

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def chartExp (c : ∀ k, ι k) (n : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun q => if q.2 = c q.1 then n q.1 else 0

def chartMon (c : ∀ k, ι k) (n : K → ℕ) : MRingOver S ι :=
  monomial (chartExp c n) 1

theorem chartMon_homog (c : ∀ k, ι k) (n : K → ℕ) : IsMultiHomog (chartMon (S := S) c n) n :=
  GenTwistGenerated.isMultiHomog_monomial _ _ _ fun k => by simp [chartExp]

theorem chartMon_mem {I : ∀ k, Finset (ι k)} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ I k) (n : K → ℕ) :
    chartMon (S := S) c n ∈ KH.cellMon S I := by
  unfold chartMon
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  refine Submonoid.prod_mem _ fun q hq => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  have hq' : q.2 = c q.1 := by
    by_contra h
    simp [chartExp, h] at hq
  obtain ⟨k, i⟩ := q
  simp only at hq'
  subst hq'
  exact ⟨k, c k, hc k, rfl⟩

variable {V : Ideal (MRingOver S ι)}

theorem smul_quot (f : MRingOver S ι) (m : MRingOver S ι ⧸ V) : f • m = Ideal.Quotient.mk V f * m := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
  rfl

theorem smul_mul_eq_mul_smul {T : Submonoid (MRingOver S ι)} (p : MRingOver S ι)
    (x y : LocalizedModule T (MRingOver S ι ⧸ V)) : (p • x) * y = x * (p • y) := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_mul_mk, LocalizedModule.smul'_mk,
        LocalizedModule.mk_mul_mk, smul_mul_assoc, mul_smul_comm]

theorem generatedV_of_generatedMod {d : K → ℤ} (h : GeneratedMod S ι (KH.quotPart S V) d) :
    KH.GeneratedV S V d := by
  classical
  intro I
  let c : ∀ k, ι k := fun k => (I.2.1 k).choose
  have hc : ∀ k, c k ∈ I.1 k := fun k => (I.2.1 k).choose_spec
  let dp : K → ℕ := fun k => (d k).toNat
  let dm : K → ℕ := fun k => (-d k).toNat
  have hd : ∀ k, (dp k : ℤ) - dm k = d k := fun k => Int.toNat_sub_toNat_neg (d k)
  let P : MRingOver S ι := chartMon c dp
  let Q : MRingOver S ι := chartMon c dm
  have hP : P ∈ KH.cellMon S I.1 := chartMon_mem hc dp
  have hQ : Q ∈ KH.cellMon S I.1 := chartMon_mem hc dm
  have hpart : ∀ (f : MRingOver S ι) (a : K → ℕ), IsMultiHomog f a →
      Ideal.Quotient.mk V f ∈ KH.quotPart S V (fun k => (a k : ℤ)) := fun f a hf =>
    Submodule.subset_span ⟨f, ⟨fun k => Int.natCast_nonneg _, by simpa using hf⟩, rfl⟩
  let x : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V P) ⟨Q, hQ⟩
  have hx : x ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) d := by
    refine GenTwistGenerated.mk_mem_locPart _ _ dm (chartMon_homog c dm) ?_
    have e : (d + fun k => (dm k : ℤ)) = fun k => (dp k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply]
      omega
    rw [e]
    exact hpart P dp (chartMon_homog c dp)
  obtain ⟨t, a, r, p, z, ht, hta, hpa, hz, htx⟩ := h I x hx
  let w : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V Q) ⟨t * P, mul_mem ht hP⟩
  refine ⟨r, z, fun j => p j • w, hz, fun j => ?_, ?_⟩
  · have e0 : p j • Ideal.Quotient.mk V Q = Ideal.Quotient.mk V (p j * Q) := by
      rw [smul_quot, map_mul]
    have e1 : p j • w =
        LocalizedModule.mk (Ideal.Quotient.mk V (p j * Q)) ⟨t * P, mul_mem ht hP⟩ :=
      (LocalizedModule.smul'_mk ..).trans (congrArg (fun m => LocalizedModule.mk m _) e0)
    refine (congrArg (· ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-d)) e1).mpr ?_
    refine GenTwistGenerated.mk_mem_locPart _ _ (a + dp)
      (GenTwistGenerated.isMultiHomog_mul hta (chartMon_homog c dp)) ?_
    have e2 : (-d + fun k => ((a + dp) k : ℤ)) = fun k => ((a + dm) k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply, Pi.neg_apply, Nat.cast_add]
      omega
    rw [e2]
    exact hpart _ _ (GenTwistGenerated.isMultiHomog_mul (hpa j) (chartMon_homog c dm))
  · calc ∑ j, p j • w * z j I = ∑ j, w * (p j • z j I) :=
          Finset.sum_congr rfl fun j _ => smul_mul_eq_mul_smul (p j) w (z j I)
      _ = w * (t • x) := by rw [← Finset.mul_sum, htx]
      _ = 1 := by
        have e3 : Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P) =
            ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) • (1 : MRingOver S ι ⧸ V)) := by
          rw [Submonoid.smul_def, smul_quot, smul_quot, mul_one]
          simp only [Submonoid.coe_mul, map_mul]
          ring
        calc w * (t • x)
            = w * LocalizedModule.mk (t • Ideal.Quotient.mk V P) ⟨Q, hQ⟩ :=
              congrArg (w * ·) (LocalizedModule.smul'_mk ..)
          _ = LocalizedModule.mk (Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P))
                (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) := LocalizedModule.mk_mul_mk
          _ = LocalizedModule.mk ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) •
                (1 : MRingOver S ι ⧸ V)) (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) :=
              congrArg (fun m => LocalizedModule.mk m _) e3
          _ = LocalizedModule.mk 1 1 := LocalizedModule.mk_cancel _ _
          _ = 1 := OreLocalization.one_def.symm

end GenerationOfH1GenAmple

theorem GenerationOfH1GenAmple.proof (hQ : QuotPartGraded.Statement) : GenerationOfH1GenAmple.Statement := by
  intro S _ K _ _ ι _ _ V N hV hH e
  have hann : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ V) := fun v hv =>
    Module.mem_annihilator.mpr fun m => by
      rw [GenerationOfH1GenAmple.smul_quot, Ideal.Quotient.eq_zero_iff_mem.mpr hv, zero_mul]
  obtain ⟨c₁, hc₁⟩ := hH (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance (hQ S K ι V hV) hann e
  exact ⟨c₁, fun c hc => GenerationOfH1GenAmple.generatedV_of_generatedMod (hc₁ c hc).2⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LeLimsupDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

namespace ArithmeticVolumeBigDimensionOne

theorem le_limsup_div {u : ℕ → ℝ} {T C C' : ℝ}
    (hlo : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * T - C ≤ u n) (hup : ∀ n : ℕ, u n ≤ C' * ((n : ℝ) + 1)) :
    T ≤ limsup (fun n : ℕ => u n / n) atTop := by
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => u n / n) := by
    refine isBoundedUnder_of_eventually_le (a := 2 * |C'|) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by linarith)]
    calc u n ≤ C' * ((n : ℝ) + 1) := hup n
      _ ≤ |C'| * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ 2 * |C'| * n := by nlinarith [abs_nonneg C']
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have key : T - ε ≤ limsup (fun n : ℕ => u n / n) atTop := by
    refine le_limsup_of_frequently_le (Eventually.frequently ?_) hb
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
    rw [le_div_iff₀ (by linarith)]
    have hC : C < n * ε := (div_lt_iff₀ hε).mp (hN.trans_le hnN)
    have hl := hlo n hn1
    nlinarith
  linarith

end ArithmeticVolumeBigDimensionOne

theorem ArithmeticVolumeBigDimensionOne.proof (hP : PackingStatement) (hL : CurveSmallCountLower.Statement) :
    ArithmeticVolumeBigDimensionOne.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII har hb hP0 hs hnef hc
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII har hb hs.1 hc
  obtain ⟨-, C', hC'⟩ := hP K ι Ω y 0 A (chartLat y A.a) har hb hs.1
    (fun τ => SmallSectionPointHeight.chartLat_le_chartLatNm y A.a τ)
  have e : arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 0 =
      limsup (fun n : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n / n) atTop := by
    unfold arVolP
    congr 1
    funext n
    simp
  rw [e]
  exact ArithmeticVolumeBigDimensionOne.le_limsup_div hC (fun n => by simpa using hC' n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBigIffGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace BigIffGenDeg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ)) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [map_natCast C n, map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot.mp hmem)

theorem coord_ne_zero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) :
    ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro k
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show mConeMap y (X ⟨k, i⟩) = 0
  simp [mConeMap, h0]

theorem proof (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement)
    (hL : SectionLatticeFinite.Statement) (hR : ChartLatRank.Statement)
    (hA : NefSectionsAsymptotic.Statement) : BigIffGenDeg.Statement := by
  intro K _ ι _ Ω _ y D M P₀ hD1 har hP0 hs
  have := charZero_of_isArithVar har
  have hy := coord_ne_zero_of_isArithVar har
  obtain ⟨C, hC⟩ := hA K ι Ω y D M.a hD1 har (nefOnGenericDeg_of_semipos hN hD hP0 hs)
  set δ : ℝ := (genDeg (mCoordIdeal y) D M.a : ℝ) with hδdef
  set F : ℝ := (D.factorial : ℝ) with hFdef
  have hF : 0 < F := by positivity
  set r : ℕ → ℕ := fun n => Module.finrank ℤ (AddSubgroup.toIntSubmodule (chartLat y M.a n)) with hrdef
  have hrank : ∀ n : ℕ, |(r n : ℝ) - δ * (n : ℝ) ^ D / F| ≤ C * ((n : ℝ) + 1) ^ (D - 1) := fun n => by
    simp only [hrdef]
    rw [hR K ι Ω y M.a n hy]
    exact hC n
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hrank 0)
    simpa using this
  have hpow : ∀ x : ℝ, 1 ≤ x → (x + 1) ^ (D - 1) ≤ 2 ^ (D - 1) * x ^ (D - 1) := fun x hx => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hsplit : ∀ x : ℝ, x ^ D = x * x ^ (D - 1) := fun x => by
    rw [← pow_succ']
    congr 1
    omega
  have hδ0 : (0 : ℤ) < genDeg (mCoordIdeal y) D M.a ↔ 0 < δ := by
    rw [hδdef]
    exact_mod_cast Iff.rfl
  rw [hδ0]
  constructor
  · rintro ⟨c, hc, j, hj, hev⟩
    by_contra hδ
    push Not at hδ
    set B : ℝ := C * 2 ^ (D - 1) * (j : ℝ) ^ (D - 1) with hB
    obtain ⟨n, ⟨q, s, hcq, hli, hmem⟩, hnN⟩ :=
      (hev.and (eventually_ge_atTop (max 1 (⌈B / c⌉₊ + 1)))).exists
    have hn1 : 1 ≤ n := le_of_max_le_left hnN
    have hnB : B < c * n := by
      have h1 : B / c < n := by
        have := Nat.le_ceil (B / c)
        have h2 : ((⌈B / c⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hnN
        push_cast at h2
        linarith
      rwa [div_lt_iff₀ hc, mul_comm] at h1
    set p := AddSubgroup.toIntSubmodule (chartLat y M.a (j * n))
    have : Module.Finite ℤ p := Module.Finite.iff_fg.mpr (by
      have := hL K ι Ω y M.a (j * n) hy
      exact (Submodule.fg_iff_addSubgroup_fg _).mpr this)
    have hle : q ≤ r (j * n) := by
      have hli' : LinearIndependent ℤ (fun i => (⟨s i, hmem i⟩ : p)) :=
        LinearIndependent.of_comp p.subtype hli
      simpa using hli'.fintype_card_le_finrank
    have hjn : (1 : ℝ) ≤ ((j * n : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hup : (r (j * n) : ℝ) ≤ B * (n : ℝ) ^ (D - 1) := by
      have h1 := le_of_abs_le (hrank (j * n))
      have h2 : δ * ((j * n : ℕ) : ℝ) ^ D / F ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hδ (by positivity)) hF.le
      have h3 := mul_le_mul_of_nonneg_left (hpow _ hjn) hC0
      have h4 : C * (2 ^ (D - 1) * ((j * n : ℕ) : ℝ) ^ (D - 1)) = B * (n : ℝ) ^ (D - 1) := by
        rw [hB]; push_cast; rw [mul_pow]; ring
      linarith
    have hq : c * (n : ℝ) ^ D ≤ B * (n : ℝ) ^ (D - 1) :=
      hcq.trans ((by exact_mod_cast hle : (q : ℝ) ≤ r (j * n)).trans hup)
    rw [hsplit, ← mul_assoc] at hq
    have hpos : 0 < (n : ℝ) ^ (D - 1) := by positivity
    exact absurd (le_of_mul_le_mul_right hq hpos) (not_le.mpr hnB)
  · intro hδ
    refine ⟨δ / (2 * F), by positivity, 1, le_rfl, ?_⟩
    set N : ℝ := 2 * F * C * 2 ^ (D - 1) / δ with hN'
    filter_upwards [eventually_ge_atTop (max 1 ⌈N⌉₊)] with n hnN
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hnN
    have hnN' : N ≤ n := (Nat.le_ceil N).trans (by exact_mod_cast le_of_max_le_right hnN)
    set p := AddSubgroup.toIntSubmodule (chartLat y M.a n)
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (le_refl (Module.finrank ℤ p))
    refine ⟨_, fun i => (f i : Ω), ?_, hf.map' p.subtype (Submodule.ker_subtype p), fun i => by
      rw [one_mul]; exact (f i).2⟩
    have h1 := neg_le_of_abs_le (hrank n)
    have h2 := mul_le_mul_of_nonneg_left (hpow _ hn1) hC0
    have h3 : C * 2 ^ (D - 1) ≤ δ / (2 * F) * n := by
      rw [hN', div_le_iff₀ hδ] at hnN'
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h4 : C * 2 ^ (D - 1) * (n : ℝ) ^ (D - 1) ≤ δ / (2 * F) * (n : ℝ) ^ D := by
      rw [hsplit, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    change δ / (2 * F) * (n : ℝ) ^ D ≤ (r n : ℝ)
    linear_combination h1 + h2 + h4

end BigIffGenDeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageTop
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockImageTop

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]

theorem isMultiHomog_blockForms (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (q : Σ k, GlobalTheory κ k) :
    IsMultiHomog (blockForms k₀ M q) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk, Sigma.ext_iff]

theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (i : ι k₀) :
    X ⟨k₀, i⟩ - ∑ j, C (N i j) * blockForms k₀ M j ∈ mCoordIdeal y := by
  have hf : ∀ j, mConeMap y (blockForms k₀ M j) = MvPolynomial.C (x j) * MvPolynomial.X k₀ := by
    intro j
    rw [h.1 j, map_sum, Finset.sum_mul]
    simp [blockForms, mConeMap, map_sum, mul_assoc]
  have hX : mConeMap y (X ⟨k₀, i⟩) = MvPolynomial.C (y ⟨k₀, i⟩) * MvPolynomial.X k₀ := by
    simp [mConeMap]
  rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_sum]
  simp only [map_mul, hf]
  rw [hX, h.2 i, map_sum, Finset.sum_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mConeMap, mul_assoc]

theorem isBasePtFree_blockForms {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) :
    IsBasePtFree (mCoordIdeal y) (blockForms k₀ M) := by
  intro k₂ i
  refine ⟨1, ?_⟩
  rw [pow_one, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k₀)]
  refine Ideal.mul_mem_right _ _ ?_
  have hspan : ∑ j, C (N (i k₀) j) * blockForms k₀ M j ∈
      Ideal.span (Set.range fun j : GlobalTheory κ k₂ => blockForms k₀ M ⟨k₂, j⟩) := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j.2, ?_⟩)
    cases k₂
    rfl
  have := Ideal.add_mem _ (Ideal.mem_sup_left (sub_mem_mCoordIdeal h (i k₀))) (Ideal.mem_sup_right hspan)
  rwa [sub_add_cancel] at this

theorem isSmoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  refine hm.mono fun z hz => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 => hi (congrFun h0 _)

theorem formApply_blockForms (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (z : (Σ k, ι k) → ℂ) :
    formApply (blockForms k₀ M) z = blockMapC k₀ M z := by
  funext q
  simp [formApply, blockForms, blockMapC]

end BlockImageTop

open BlockImageTop in

theorem BlockImageTop.proof (hCM : GraphChangeOfModel.Statement) (hIm : BlockGraphImage.Statement)
    (hDeg : BlockGraphDeg.Statement) : BlockImageTop.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ I y k₀ A M N x m hI hP hB hx hBI ha hA hm hh
  obtain ⟨G, J, hJ, hJ1⟩ := hDeg D K ι Ω κ y k₀ M N x hP hB hx hBI
  have himg := hIm K ι Ω κ y k₀ M N x hBI
  have key := hCM I hI K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) G J
    (fun _ => HermLine.ofCone m) (fun _ => A) hP (isMultiHomog_blockForms k₀ M) (isBasePtFree_blockForms hBI)
    (by rw [himg]; exact hx) hJ (fun _ => isSmoothHerm_ofCone hm) (fun _ => hA)
    (fun _ k => by
      rw [ha]
      by_cases hk : k = k₀ <;> simp [unitDeg, blockDeg, HermLine.ofCone, hk])
    (fun _ z hz => by rw [hh z hz, formApply_blockForms]; rfl)
  rw [himg, hJ1] at key
  simpa [top] using key

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedProductNonneg

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_of_mem_support_ratDiv {V : Ideal (MRingOver F ι)} {f g : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (hW : W ∈ (ratDiv V f g).support) : V ≤ W := by
  have key : ∀ s : MRingOver F ι, ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → V ≤ W := by
    intro s hs
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at hs
    rw [Finsupp.ofSupportFinite_coe] at hs
    split_ifs at hs with h
    · exact le_sup_left.trans h.1.1.2
    · exact absurd rfl hs
  rw [Finsupp.mem_support_iff, ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g fun h => hW ?_
    rw [hf, h]
    simp
  · exact key f hf

end GeneratedProductNonneg

theorem GeneratedProductNonneg.proof (hR : GeneratedRestrict.Statement)
    (hE : GeneratedEffectiveSection.Statement) : GeneratedProductNonneg.Statement := by
  classical
  intro F _ K _ _ ι _ _ I V m β hI hV hgen
  induction m generalizing V with
  | zero =>
    choose i hi using hV.1.2.2
    rw [hI.1 V β i hV hi]
    exact Int.natCast_nonneg _
  | succ m ih =>
    obtain ⟨f, g, hs, heff⟩ := hE F K ι V (β (Fin.last m)) hV.1 (hgen (Fin.last m))
    have e := hI.2 V m (Fin.init β) (β (Fin.last m)) f g hV hs
    rw [Fin.snoc_init_self] at e
    rw [e, cycEval]
    refine Finsupp.sum_nonneg fun W hW => mul_nonneg (heff W) ?_
    obtain ⟨α, γ, hf, hg, hfV, hgV, -⟩ := hs
    have hWm : IsProjVarF W m := KleimanNefF.isProjVarF_of_mem_support hV
      ((NumbersDVR.VocabMultiHomog.proof F K ι f α).1 hf) ((NumbersDVR.VocabMultiHomog.proof F K ι g γ).1 hg)
      hfV hgV hW
    have hle : V ≤ W := GeneratedProductNonneg.le_of_mem_support_ratDiv hW
    exact ih W (Fin.init β) hWm fun j => hR F K ι V W _ hle (hgen _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSemiampleNef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SemiampleNef.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (a : K → ℤ),
    IndefiniteRowSideFullHecke.HilbertSamuel.IsSemiampleOnFibres P a → NefOnFibres P a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

