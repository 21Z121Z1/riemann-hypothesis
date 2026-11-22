import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0110
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0131
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0152

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevTwist

theorem conjP_ne {R : Ranks} (H : Formalism.BasicNotions.Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : conjPrime₂ P ≠ P := by
  intro e
  obtain ⟨x, hx, hy⟩ := h
  have hc : IsConjPl H P P := (isConjPl_iff H P P).2 e.symm
  have e1 : ((cO H.E x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := bridge_star_holds R H x
  exact hy _ e1 ((hc x _ e1).1 hx)

variable {B : Base} {X : PreX B.toPre} {I : ColIn B X}

theorem under_sel (h : I.Ok) (v : HeightOneSpectrum (𝓞 B.host.F)) : (I.sel v).under (𝓞 B.host.F) = v :=
  HeightOneSpectrum.ext (h.sel_ok v)

theorem good_of_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ I.SQ) :
    I.sel (P.under (𝓞 B.host.F)) = P ∧ GoodPl B.host.E I.S (P.under (𝓞 B.host.F)) := by
  obtain ⟨a, ha⟩ := I.mem_SQ.1 hP
  obtain ⟨v, -, rfl, hg⟩ := I.exists_of_mem_Q ha
  rw [under_sel h]
  exact ⟨rfl, hg⟩

theorem plc_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ (B.primes X).vGs) :
    Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 B.host.F)) ∈ I.S := by
  classical
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have h0 : ∀ i, B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun i h => by
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hm : ∃ i, B.fields.conjO ((B.primes X).piG i) ∈ P.asIdeal := by
    unfold Primes.vGs Primes.vG at hP
    simpa only [Finset.mem_union, mem_divs (h0 _), Fin.exists_fin_two] using hP
  obtain ⟨i, hi⟩ := hm
  have h1 : ((B.primes X).g i : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hPr.piG_norm i]; exact Ideal.mul_mem_left _ _ hi
  rw [(ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.g_prime i)).2 h1]
  exact h.g_mem i

theorem levOk_twists : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → LevOk B.host (B.primes X).vGs I.SQ ∧ Disjoint (B.primes X).vGs I.SQ ∧ ∀ a, KDq B.host (I.Q a) ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker ∧ (I.xi a).IsUnitary := by
  classical
  intro B X I h
  have hb := levOk_base B X
  have hu : ∀ P : HeightOneSpectrum (𝓞 B.host.E), (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := fun P =>
    (under_eq_iff B.host P _).2 (Or.inr rfl)
  refine ⟨⟨hb.cover, fun P hP hP' => ?_⟩, Finset.disjoint_left.2 fun P h1 h2 => (good_of_mem h h2).2.2.2 (plc_mem h h1),
    fun a => ?_⟩
  · simp only [Finset.mem_union] at hP hP'
    rcases hP with hP | hP <;> rcases hP' with hP' | hP'
    · exact hb.split P (by simpa using hP) (by simpa using hP')
    · refine (good_of_mem h hP').2.2.2 ?_
      rw [hu]
      exact plc_mem h hP
    · refine (good_of_mem h hP).2.2.2 ?_
      rw [← hu]
      exact plc_mem h hP'
    · have e := (good_of_mem h hP').1
      rw [hu, (good_of_mem h hP).1] at e
      exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 (good_of_mem h hP).2).1 e.symm
  · obtain ⟨⟨⟨n, hn, ho⟩, hT, hta, -⟩, hq, -⟩ :=
      ReadTwist.isTwist_of_reads B.R B.host B.LL B.embLL I.S (I.tup a) (I.xi a) (h.xi_reads a)
    refine ⟨KDq_le_ker_of_tame _ hT hta fun w hw => by_contra fun hr => hw (Or.inr ?_), fun x => ?_⟩
    · have hfin : (Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K)).Finite :=
        ((UnrAe.finite_ramified (I.xi a)).image (·.under (𝓞 B.host.F))).subset fun v hv => by
          obtain ⟨P, e, hP⟩ := (hq v).1 hv
          exact ⟨P, hP, e⟩
      have hmem : I.sel (w.under (𝓞 B.host.F)) ∈ I.Q a := by
        unfold ColIn.Q QE
        rw [dif_pos hfin]
        convert Finset.mem_image_of_mem I.sel (hfin.mem_toFinset.2 ((hq _).2 ⟨w, rfl, hr⟩))
      rcases (under_eq_iff B.host _ w).1 (under_sel h _).symm with e | e
      · exact Or.inl (e ▸ hmem)
      · exact Or.inr ⟨_, hmem, (isConjPl_iff B.host _ _).2 e⟩
    · have h1 : (I.xi a).1 x ^ n = 1 := congrArg (fun χ : HChar B.host.E => χ.1 x) ho
      have h2 : ‖(((I.xi a).1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
        rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

end GlobalTheory.Mem.LevTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaximalIdealIffNormLtOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.IntMaxFinExt

theorem mem_maximalIdeal_iff_norm_lt_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) [IsLocalRing ↥(Loc.OL K)] (y : ↥(Loc.OL K)), y ∈ IsLocalRing.maximalIdeal ↥(Loc.OL K) ↔ ‖((y : ↥K.1) : PadicAlgCl l)‖ < 1 := by
  intro l _ K _ y
  have hle : ∀ z : ↥(Loc.OL K), ‖((z : ↥K.1) : PadicAlgCl l)‖ ≤ 1 := fun z =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K (z : ↥K.1)).1 z.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hlt
    have h1 : ‖((y : ↥K.1) : PadicAlgCl l)‖ = 1 := le_antisymm (hle y) (not_lt.1 hlt)
    have hy0 : (y : ↥K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    have hinv : ((y : ↥K.1)⁻¹ : ↥K.1) ∈ Loc.OL K := by
      rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
      rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
    apply hnu
    refine ⟨⟨y, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show (y : ↥K.1) * (y : ↥K.1)⁻¹ = 1
      exact mul_inv_cancel₀ hy0
    · apply Subtype.ext
      show (y : ↥K.1)⁻¹ * (y : ↥K.1) = 1
      exact inv_mul_cancel₀ hy0
  · intro hlt hu
    obtain ⟨u, rfl⟩ := hu
    have hm : ((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l)) * ((((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l) = 1 := by
      have := congrArg (fun z : ↥(Loc.OL K) => (((z : ↥K.1)) : PadicAlgCl l)) u.mul_inv
      exact this
    have hn := congrArg norm hm
    rw [norm_mul, norm_one] at hn
    have h2 := hle ((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K))
    have h0 : 0 ≤ ‖((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l))‖ := norm_nonneg _
    nlinarith

end GlobalTheory.IntMaxFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MkDetPtEqRelDetQ
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.Mem.Chr.RelDet GlobalTheory.Mem.Chr.IdlFact
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetLat

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem ordSub_conj {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ P) (detSub N) = -ordSub P (detSub N) := by
  have h := CharValCompare.val_dual (P := P) ⟨hN, hu⟩ (isFr_latFr P hN) (isFr_latFr (conjPrime₂ P) hN)
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq hN (isFr_latFr P hN), ordSub_detSub_eq hN (isFr_latFr (conjPrime₂ P) hN)]
  unfold ordF
  rw [eq_inv_of_mul_eq_one_right h, WithZero.log_inv]

theorem ordSub_std (w : HeightOneSpectrum (𝓞 E)) : ordSub w (detSub (stdLat E n)) = 0 := by
  rw [ordSub_detSub_eq (f := 1) stdLat_lattice fun _ => Iff.rfl]
  simp [ordF]

open Classical in

theorem ordI_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    {fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n} (hf : ∀ P, IsFr P N (fr P)) (w : HeightOneSpectrum (𝓞 E)) :
    ordI w (detIdl SB N fr) =
      if w ∈ SB then ordSub w (detSub N) else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub N)).toNat : ℤ) := by
  have e : valAt w (detIdl SB N fr) = Valued.v (compAt w (detIdl SB N fr)) := valAt_apply _ _
  rw [ordI, e, compAt_detIdl SB hN]
  split_ifs
  · rw [valued_algebraMap, ordSub_detSub_eq hN (hf w)]
    rfl
  · simp
  · have h := ordF_unif_self w
    unfold ordF at h
    rw [map_pow, valued_algebraMap, WithZero.log_pow, neg_eq_iff_eq_neg.1 h]
    simp

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_mk_eq_of_ord {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {a b : Ideles H.E}
    (h : ∀ w, ordI w a - ordI (conjPrime₂ w) a = ordI w b - ordI (conjPrime₂ w) b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtQ H SQ ⧸ UOQ H SQ) = QuotientGroup.mk (QuotientGroup.mk b) := by
  refine QuotientGroup.eq.2 ?_
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mk_mem_UOQ, KDq_sup_unitIdl]
  refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
  rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv,
    (isConjPl_iff H w w').1 hw]
  have := h w
  congr 1
  omega

end GlobalTheory.Mem.Col2.DetLat

namespace GlobalTheory.Mem.Col2

open DetLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_detPt_eq_relDetQ : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → (QuotientGroup.mk (detPt H SQ p) : DtQ H SQ ⧸ UOQ H SQ) = relDetQ H SQ n (stdLat H.E n) p.deco.1.N := by
  intro R H n ST SG Q SQ p hL
  have hN := p.deco.2.lat
  have hf : {w | (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat ≠ 0}.Finite :=
    (finite_ordSub hN).subset fun v hv h0 => hv (by simp [h0, ordSub_std])
  refine mk_mk_eq_of_ord H SQ (a := ptIdl H SQ p)
    (b := powI fun w => (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat) fun w => ?_
  rw [ordI_powI _ hf, ordI_powI _ hf, ptIdl, ordI_detIdl _ hN (isFr_ptFr p), ordI_detIdl _ hN (isFr_ptFr p),
    CharValCompare.conjP_conjP, ordSub_std, ordSub_std, ordSub_conj hN p.deco.2.uni]
  have hs := hL.split w
  by_cases h1 : w ∈ uSG SG SQ
  · rw [if_pos h1, if_neg (hs h1), if_pos h1]
    omega
  · by_cases h2 : conjPrime₂ w ∈ uSG SG SQ
    · rw [if_neg h1, if_pos h2, if_pos h2]
      omega
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
      omega

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicativeWeightPrimeSumStatement
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_weight_prime_sum : GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ m₀ a₀ : ℕ, 8 ∣ m₀ → 0 < m₀ → Nat.Coprime a₀ m₀ → a₀ % 4 = 3 → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ x ^ (400 : ℝ) < p) → ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → ∀ κ : ℕ → ℂ, κ 1 = 1 → (∀ m n, κ (m * n) = κ m * κ n) → (∀ n, ‖κ n‖ ≤ 1) → (∑ p ∈ Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X, ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x κ p‖ ^ 2) / (Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X).card ≤ C * x * Real.log x := by
  first | exact @GlobalTheory.Mem.An.meanSq_primes_residue_le | exact GlobalTheory.Mem.An.meanSq_primes_residue_le | (intros; apply GlobalTheory.Mem.An.meanSq_primes_residue_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesDyadicLowerBound
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.ManyNormPrimes

lemma ev_log_sq (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ x ^ (eps / 5) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := eps / 5) 2 (by positivity)).bound one_pos
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx h1
  have h0 : (0 : ℝ) ≤ x ^ (eps / 5) := Real.rpow_nonneg (by linarith) _
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg h0, one_mul] at hx
  exact hx

lemma ev_exp (C c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, C * Real.exp (-c * t) ≤ δ := by
  have h1 : Tendsto (fun t : ℝ => -c * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul C
  rw [mul_zero] at h2
  exact (h2.eventually (ge_mem_nhds hδ))

lemma core (C₀ Cr cr c t B Y : ℝ) (hC₀ : 0 < C₀) (hCr : 0 < Cr) (hcr : 0 < cr) (hc : 0 < c)
    (ht : 10000 ≤ t) (htC : C₀ ≤ t) (h1 : Cr * Real.exp (-cr * t) ≤ 1 / 200)
    (h2 : 40 * Real.exp (-(1 / 20) * t) ≤ c) (hB : 1 < B) (hBt : Real.log B ≤ 8 * t ^ 2)
    (hY : 0 < Y) (hYt : 8 * t ^ 5 ≤ Real.log Y) :
    B ^ C₀ ≤ Y ∧ Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr B Y ≤ 1 / 100 ∧ B ^ (7 : ℝ) ≤ 1 * Y ^ ((1 : ℝ) / 3) ∧
      Y ^ ((9 : ℝ) / 10) ≤ c * 1 * B ^ (-6 : ℝ) * Y / Real.log Y := by
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos hB
  set L := Real.log Y with hL
  set b := Real.log B with hb
  have ht1 : 1 ≤ t := by linarith
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have ht3 : 10000 * t ≤ t ^ 3 := by nlinarith
  have ht5 : t ^ 5 = t ^ 3 * t ^ 2 := by ring
  have hbL : 10000 * t * b ≤ L := by
    have : 10000 * t * b ≤ t ^ 3 * (8 * t ^ 2) :=
      mul_le_mul ht3 hBt hlB.le (by positivity)
    nlinarith
  have htb : b ≤ t * b := by nlinarith
  have ht2L : t ^ 2 ≤ L := by
    have : t ^ 2 ≤ t ^ 5 := pow_le_pow_right₀ ht1 (by norm_num)
    nlinarith [sq_nonneg t]
  have hL0 : 0 < L := by linarith
  have hYe : Y = Real.exp L := (Real.exp_log hY).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hB0, hYe]
    apply Real.exp_le_exp.2
    nlinarith
  · unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have e1 : -cr * L / b ≤ -cr * t := by
      rw [div_le_iff₀ hlB]
      have : t * b ≤ L := by nlinarith
      nlinarith
    have e2 : -cr * √L ≤ -cr * t := by
      have : t ≤ √L := Real.le_sqrt_of_sq_le ht2L
      nlinarith
    have f1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 e1) hCr.le
    have f2 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 e2) hCr.le
    linarith
  · rw [Real.rpow_def_of_pos hB0, Real.rpow_def_of_pos hY, one_mul]
    apply Real.exp_le_exp.2
    nlinarith
  · rw [Real.rpow_def_of_pos hB0, Real.rpow_def_of_pos hY, mul_one, le_div_iff₀ hL0, ← hL, ← hb]
    have g1 : L ≤ 40 * Real.exp (L / 40) := by
      have := Real.add_one_le_exp (L / 40)
      linarith
    have g2 : 40 * Real.exp (-(1 / 20) * L) ≤ c := by
      have : Real.exp (-(1 / 20) * L) ≤ Real.exp (-(1 / 20) * t) := Real.exp_le_exp.2 (by linarith)
      linarith
    calc Real.exp (L * (9 / 10)) * L ≤ Real.exp (L * (9 / 10)) * (40 * Real.exp (L / 40)) := by gcongr
      _ = 40 * Real.exp (L * (9 / 10) + L / 40) := by rw [Real.exp_add]; ring
      _ ≤ 40 * Real.exp (-(1 / 20) * L + b * (-6) + L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
          linarith
      _ = 40 * Real.exp (-(1 / 20) * L) * Real.exp (b * (-6)) * Real.exp L := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ c * Real.exp (b * (-6)) * Real.exp L := by gcongr
      _ = c * Real.exp (b * (-6)) * Y := by rw [← hYe]

theorem many_norm_primes : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n q d : ℕ, 1 ≤ n → Rowq x eps n q d → ∀ Y : ℝ, 0 < Y → 8 * x ^ eps ≤ Real.log Y → Y ^ ((9 : ℝ) / 10) ≤ ((normPrimes d (4 * n * q * d) Y (2 * Y)).card : ℝ) := by
  intro hTZ eps he _
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, H⟩ := GlobalTheory.T.norm_primes_short_interval_lower hTZ
  have hT : Tendsto (fun x : ℝ => x ^ (eps / 5)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have E : ∀ᶠ t : ℝ in atTop, 10000 ≤ t ∧ C₀ ≤ t ∧ Cr * Real.exp (-cr * t) ≤ 1 / 200 ∧
      40 * Real.exp (-(1 / 20) * t) ≤ c := by
    filter_upwards [eventually_ge_atTop 10000, eventually_ge_atTop C₀,
      ev_exp Cr cr (1 / 200) hcr (by norm_num), ev_exp 40 (1 / 20) c (by norm_num) hc] with t a b c d
    exact ⟨a, b, c, d⟩
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    ((hT.eventually E).and ((ev_log_sq eps he).and (hlog.and (eventually_gt_atTop (0 : ℝ)))))
  refine ⟨x₀, fun x hx n q d hn hR Y hY hYx => ?_⟩
  obtain ⟨⟨t1, t2, t3, t4⟩, hl, hl1, hx0⟩ := hx₀ x hx
  obtain ⟨hq, -, -, -, hd, hd16, hdl, -, -, -, hN⟩ := hR
  have hxe : x ^ eps = (x ^ (eps / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  unfold GlobalTheoryTheory.X2 at hdl
  set t := x ^ (eps / 5) with ht
  have hd100 : 100 ≤ d := by
    have a1 : t ≤ t * Real.log x ^ 2 :=
      le_mul_of_one_le_right (by linarith) (one_le_pow₀ hl1)
    have a2 := Real.add_one_le_exp (t * Real.log x ^ 2)
    have a3 : (100 : ℝ) ≤ √(Real.exp (t * Real.log x ^ 2)) :=
      Real.le_sqrt_of_sq_le (by linarith)
    have : (100 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hM : 4 * d ≤ 4 * n * q * d := by
    have : 1 ≤ n * q := Nat.mul_pos hn hq1
    nlinarith
  set M : ℕ := 4 * n * q * d with hMdef
  have hMc : (M : ℝ) = 4 * n * q * d := by rw [hMdef]; push_cast; ring
  rw [← hMc] at hN
  have hMr : 4 * (d : ℝ) ≤ M := by exact_mod_cast hM
  have hdr : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hB1 : (1 : ℝ) < 4 * (d : ℝ) * (M : ℝ) ^ 2 := by nlinarith
  have hBt : Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ 8 * t ^ 2 := by
    have b1 : 4 * (d : ℝ) * (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 3 := by nlinarith [sq_nonneg (M : ℝ)]
    have b2 := Real.log_le_log (by linarith) b1
    rw [Real.log_pow] at b2
    push_cast at b2
    nlinarith
  obtain ⟨k1, k2, k3, k4⟩ := core C₀ Cr cr c t _ Y hC₀ hCr hcr hc t1 t2 t3 t4 hB1 hBt hY
    (by rw [← hxe]; exact hYx)
  have := H d M hd (by omega) hd100 (by omega) Y 1 k1 le_rfl k2 k3
  rw [show Y * (1 + 1) = 2 * Y by ring] at this
  exact k4.trans this

end GlobalTheory.Mem.An.ManyNormPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaDensityScale

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c' = c := by
  obtain ⟨l, hl, ht⟩ := h
  obtain ⟨l', hl', ht'⟩ := h'
  have e : l = l' := GlobalTheory.OmegaLebUnique.omegaLeb_unique P Q l l' hl hl'
  subst e
  exact tendsto_nhds_unique ht' ht

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal}
    (h : OmegaDensity μ c) (a : NNReal) : OmegaDensity ((a : ENNReal) • μ) (a * c) := by
  obtain ⟨l, hl, ht⟩ := h
  refine ⟨l, hl, ?_⟩
  have h2 := ENNReal.Tendsto.const_mul (a := (a : ENNReal)) ht (Or.inr ENNReal.coe_ne_top)
  refine h2.congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

theorem omegaDensity_unique_and_smul : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)) (c : ENNReal),
    OmegaDensity μ c → (∀ c', OmegaDensity μ c' → c' = c) ∧
      ∀ a : NNReal, OmegaDensity ((a : ENNReal) • μ) (a * c) :=
  fun _ _ _ _ h => ⟨fun _ h' => omegaDensity_unique h h', fun a => omegaDensity_smul h a⟩

end GlobalTheory.OmegaDensityScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDeXExpandStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_DeX_expand_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  first | exact @GlobalTheory.WeylLatDualProof.phi_DeX_expand | exact GlobalTheory.WeylLatDualProof.phi_DeX_expand | (intros; apply GlobalTheory.WeylLatDualProof.phi_DeX_expand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Proportional
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {X W T : Scheme.{0}} {L : LB X} {m : ℕ}

def Generates (J : X.IdealSheafData) (σ : Fin (m + 1) → L.Sec) : Prop :=
  (⨆ k, L.U k = ⊤) ∧ ∀ (k : L.ι) (V : X.affineOpens) (h : V.1 ≤ L.U k),
    J.ideal V = Ideal.span (Set.range fun j => resG X h ((σ j).f k))

def Proportional (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) : Prop :=
  ∀ (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : Fin (m + 1)) (hi : A ≤ ψ ⁻¹ᵁ chart R m i) (j : Fin (m + 1)),
    (g.appLE (L.U k) A hk).hom ((σ j).f k) = pullRatio ψ A i hi j * (g.appLE (L.U k) A hk).hom ((σ i).f k)

theorem Proportional.comp {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (h : Proportional σ g ψ)
    (d : T ⟶ W) : Proportional σ (d ≫ g) (d ≫ ψ) := by
  intro A k hk i hi j
  have hA : A ≤ d ⁻¹ᵁ (g ⁻¹ᵁ L.U k ⊓ ψ ⁻¹ᵁ chart R m i) := fun x hx => ⟨hk hx, hi hx⟩
  have := congrArg (d.appLE _ A hA).hom (h _ k inf_le_left i inf_le_right j)
  rwa [map_mul, appLE_appLE, appLE_appLE, appLE_pullRatio] at this

theorem Proportional.of_comp {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (d : T ⟶ W)
    [IsSchemeTheoreticallyDominant d] [QuasiCompact d] (h : Proportional σ (d ≫ g) (d ≫ ψ)) :
    Proportional σ g ψ := by
  intro A k hk i hi j
  apply d.app_injective A
  rw [Scheme.Hom.app_eq_appLE, map_mul, appLE_appLE, appLE_appLE, appLE_pullRatio]
  exact h _ k _ i _ j

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0ZeroFreeRegionBoundStatement
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_psi0_le_exp_sqrt_log : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∃ C c : ℝ, 0 < c ∧ ∀ u : ℝ, 2 ≤ u → ‖GlobalTheoryTheory.psi0 χ u‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  first | exact @GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log | exact GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log | (intros; apply GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiPowerSavingBoundStatement
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_chi_power_saving_bound : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, 2 ≤ u → ‖psiChi χ u‖ ≤ C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2) := by
  first | exact @GlobalTheory.Mem.An.GoodBound.psiChi_bound_of_goodFor | exact GlobalTheory.Mem.An.GoodBound.psiChi_bound_of_goodFor | (intros; apply GlobalTheory.Mem.An.GoodBound.psiChi_bound_of_goodFor <;> assumption)
end

