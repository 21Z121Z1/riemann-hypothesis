import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0360
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0040
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassSumDenominatorBoundOfCmThetaHypotheses
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.DenomBound

theorem sum_val_log_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (n : ℕ) :
    ∑ l ∈ S, (padicValNat l n : ℝ) * Real.log l ≤ Real.log n := by
  rw [Real.log_nat_eq_sum_factorization,
    Finsupp.sum_of_support_subset _ (Finset.subset_union_right (s₁ := S)) _ (by simp)]
  rw [← Finset.sum_congr rfl fun (l : ℕ) (hl : l ∈ S) =>
    congrArg (fun t : ℕ => (t : ℝ) * Real.log l) (Nat.factorization_def n (hS l hl))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun l _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem log_order_le (x : ℕ) (hx : 2 ≤ x) :
    Real.log ((8 ^ (2 * x) * (4 * x).factorial : ℕ) : ℝ) ≤ 18 * x * Real.log x := by
  have h1 : 8 ^ (2 * x) ≤ x ^ (6 * x) := by
    rw [show 6 * x = 3 * (2 * x) by ring, pow_mul x]
    exact Nat.pow_le_pow_left (by simpa using Nat.pow_le_pow_left hx 3) _
  have h2 : (4 * x).factorial ≤ x ^ (12 * x) := by
    refine (Nat.factorial_le_pow _).trans ?_
    rw [show 12 * x = 3 * (4 * x) by ring, pow_mul x]
    refine Nat.pow_le_pow_left ?_ _
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hx 2)
  have h3 : 8 ^ (2 * x) * (4 * x).factorial ≤ x ^ (18 * x) := by
    rw [show 18 * x = 6 * x + 12 * x by ring, pow_add]
    exact Nat.mul_le_mul h1 h2
  calc _ ≤ Real.log ((x ^ (18 * x) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast h3)
    _ = _ := by rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

noncomputable def expo_vp (f N d Q : ℕ) (B : ℝ) (dl : ℕ → ℝ) (p : ℕ) : ℝ :=
  (padicValNat p (8 ^ (4 * f * N) * (8 * f * N).factorial) : ℝ) +
    4 * f * N * B * (dl p + (if p = d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) +
    4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ)

theorem exists_exponents (f N d Q : ℕ) (B L : ℝ) (S : Finset ℕ) (dl : ℕ → ℝ) (hf : 1 ≤ f) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hL : 1 ≤ L) (hQ : 0 < Q) (h0 : ∀ l, 0 ≤ dl l) (hz : ∀ l, l ∉ S → dl l = 0)
    (hs : ∑ l ∈ S, dl l * Real.log l ≤ L) (hd : Real.log d ≤ 2 * L) :
    ∃ S' : Finset ℕ, Exponents S' (fun p => if p.Prime then expo_vp f N d Q B dl p else 0) (intBound 18 f N B L Q) := by
  set M : ℕ := 8 ^ (4 * f * N) * (8 * f * N).factorial with hM
  have hM0 : M ≠ 0 := by positivity
  set S' : Finset ℕ := (M.primeFactors ∪ S ∪ {d} ∪ Q.primeFactors).filter Nat.Prime with hS'
  have hP : ∀ l ∈ S', l.Prime := fun l hl => (Finset.mem_filter.1 hl).2
  refine ⟨S', hP, fun l => ?_, fun l hl => ?_, ?_⟩
  · have := h0 l
    have hB0 : 0 ≤ B := by linarith
    unfold expo_vp
    dsimp only
    split_ifs <;> positivity
  · dsimp only
    split_ifs with hp
    · simp only [hS', Finset.mem_filter, hp, and_true, Finset.mem_union, not_or, Finset.mem_singleton,
        Nat.mem_primeFactors, true_and, ne_eq, hM0, hQ.ne', not_false_eq_true] at hl
      obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hl
      unfold expo_vp
      rw [← hM, padicValNat.eq_zero_of_not_dvd a1, padicValNat.eq_zero_of_not_dvd a4, hz l a2, if_neg a3]
      simp
    · rfl
  · have e1 := sum_val_log_le S' hP M
    have e2 := sum_val_log_le S' hP Q
    have e3 : ∑ l ∈ S', dl l * Real.log l ≤ L := by
      refine le_trans ?_ hs
      rw [Finset.sum_subset (s₁ := S) (s₂ := S ∪ S') Finset.subset_union_left (fun l _ hl => by rw [hz l hl, zero_mul])]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun l _ _ =>
        mul_nonneg (h0 l) (Real.log_natCast_nonneg _)
    have e4 : ∑ l ∈ S', (if l = d then (1 / 4 : ℝ) else 0) * Real.log l ≤ L / 2 := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq']
      split_ifs <;> linarith
    have e5 : Real.log M ≤ 18 * (f * (2 * N)) * Real.log (f * (2 * N)) := by
      have := log_order_le (f * (2 * N)) (by nlinarith)
      rw [show 2 * (f * (2 * N)) = 4 * f * N by ring, show 4 * (f * (2 * N)) = 8 * f * N by ring, ← hM] at this
      push_cast at this
      exact this
    have e6 : ∑ l ∈ S', (if l.Prime then expo_vp f N d Q B dl l else 0) * Real.log l =
        ∑ l ∈ S', (padicValNat l M : ℝ) * Real.log l + 4 * f * N * B * (∑ l ∈ S', dl l * Real.log l +
          ∑ l ∈ S', (if l = d then (1 / 4 : ℝ) else 0) * Real.log l + ∑ l ∈ S', (padicValNat l Q : ℝ) * Real.log l) +
          4 * (N : ℝ) ^ 2 * ∑ l ∈ S', (padicValNat l Q : ℝ) * Real.log l := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [if_pos (hP l hl), expo_vp, ← hM]
      ring
    have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hq : 0 ≤ Real.log Q := Real.log_natCast_nonneg _
    have hc : 0 ≤ 4 * (f : ℝ) * N * B := by positivity
    have hfB : 1 ≤ (f : ℝ) * B := by nlinarith
    have g1 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add e3 e4) e2) hc
    have g2 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ 4 * (N : ℝ) ^ 2 by positivity)
    have g3 : (N : ℝ) * (f * N * B * Real.log Q) ≥ 1 * (f * N * B * Real.log Q) :=
      mul_le_mul_of_nonneg_right hNR (by positivity)
    have g4 : (f : ℝ) * B * (N ^ 2 * Real.log Q) ≥ 1 * (N ^ 2 * Real.log Q) :=
      mul_le_mul_of_nonneg_right hfB (by positivity)
    have g5 : 0 ≤ (f : ℝ) * N * B * L := by positivity
    have g6 : 0 ≤ (f : ℝ) * N ^ 2 * B * Real.log Q := by positivity
    show ∑ l ∈ S', (if l.Prime then expo_vp f N d Q B dl l else 0) * Real.log l ≤ _
    rw [e6, intBound]
    nlinarith

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  have := w.isMaximal
  obtain ⟨p, n, -, h, hp, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
  exact ⟨p, hp, h⟩

theorem intSt_of_forall_inp : (∀ D, Inp D) → IntSt := by
  intro hI
  refine ⟨18, by norm_num, fun D Q N B L hQ hN hB hL hr => ?_⟩
  obtain ⟨⟨S, dl, hLet⟩, hd, -, hf, -⟩ := letters_and_sizes D (hI D).g1
  obtain ⟨S', hE⟩ := exists_exponents (fF D) N D.host.d Q B L S dl hf hN hB hL hQ.1 hLet.2.1 hLet.2.2.1
    (hLet.2.2.2.1.trans hr) (by linarith)
  refine ⟨S', _, hE, ?_, ?_⟩
  · intro δ t0 p hp Q' hQ' P hP
    have := CoordBound.coordInt D (hI D) S dl hLet Q N B hQ (by linarith) δ t0 p Q' hQ' P hP
    simp only [if_pos hp.out]
    exact this
  · intro δ t0 K _ _ _ _ σ ι P P' zA zA' hs hc hn
    have ne : ∀ (R : Pair D ⊤ δ t0 Q) (z : K), (∃ h T, R.coord h T ≠ 0) → σ z = (R.norm : ℂ) → z ≠ 0 := by
      rintro R z h1 h2 rfl
      have := (RepInv.rep_indep D (hI D) ⊤ δ t0 Q R.crv R.pt0 R R.level_pos).2.2.2.2 h1
      rw [map_zero] at h2
      exact this.ne (by exact_mod_cast h2)
    have val : ∀ (R : Pair D ⊤ δ t0 Q) (z : K), R.Small N B → z ≠ 0 → σ z = (R.norm : ℂ) → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K,
        -(3 * Formalism.PairingDivisionLocalBalance.wt S' (fun p => if p.Prime then expo_vp (fF D) N D.host.d Q B dl p else 0) w) ≤
          (Formalism.DivisionValues.vw w z : ℝ) := by
      intro R z h1 h2 h3 w
      obtain ⟨p, hp, hw⟩ := exists_prime_mem w
      have : Fact p.Prime := ⟨hp⟩
      rw [hE.wt_eq hp w hw, if_pos hp, ← mul_assoc]
      refine GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ z p w _ h2 hw fun lam => ?_
      rw [h3]
      exact (GlobalTheory.T.definiteThetaPairNorm_padicValuation_bound D (hI D) S dl hLet δ t0 Q R.crv R.pt0 hQ R N B h1 p lam).2
    refine ⟨hE.wt_size.1, hE.wt_size.2, fun i => ?_⟩
    have a1 := ne _ _ (hc i).1 (hn i).1
    have a2 := ne _ _ (hc i).2 (hn i).2
    exact ⟨a1, a2, fun w => ⟨val _ _ (hs i).1 a1 (hn i).1 w, val _ _ (hs i).2 a2 (hn i).2 w⟩⟩

end GlobalTheory.NormSum.DenomBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
section
noncomputable section

namespace GlobalTheory.FlatLine

theorem isAlgebraic_of_norm_const {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Algebra K ℂ]
    (P₀ : Ω →ₐ[K] ℂ) {b : Ω} (h : ∀ P : Ω →ₐ[K] ℂ, ‖P b‖ = ‖P₀ b‖) : IsAlgebraic K b := by
  by_contra hb
  have hi : AlgebraicIndepOn K id ({b} : Set Ω) := algebraicIndependent_unique_type_iff.2 hb
  obtain ⟨T, hT, hbas⟩ := exists_isTranscendenceBasis_superset hi
  have hw : AlgebraicIndependent K fun i : T => P₀ i := hbas.1.map' P₀.injective
  have hw2 : AlgebraicIndependent K fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (2 : K) * Polynomial.X) :=
    hw.polynomial_aeval_of_transcendental fun _ => Polynomial.transcendental _
      (by rw [Polynomial.natDegree_C_mul_X _ two_ne_zero]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero two_ne_zero)
  letI : Algebra (MvPolynomial T K) Ω := (MvPolynomial.aeval fun i : T => (i : Ω)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial T K) ℂ := (MvPolynomial.aeval fun i : T =>
    Polynomial.aeval (P₀ i) (Polynomial.C (2 : K) * Polynomial.X)).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial T K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hbas.1
  haveI : FaithfulSMul (MvPolynomial T K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hw2
  haveI : Algebra.IsAlgebraic (MvPolynomial T K) Ω :=
    haveI := hbas.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hbas.1.aevalEquiv.symm.toRingHom) (g := RingHom.id Ω)
      (Algebra.IsAlgebraic.isAlgebraic y) hbas.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hbas.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra]))⟩
  let Q : Ω →ₐ[MvPolynomial T K] ℂ := IsAlgClosed.lift
  let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
    commutes' := fun a => by
      have := Q.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using this }
  have h1 : P b = 2 * P₀ b := by
    show Q b = _
    have := Q.commutes (MvPolynomial.X ⟨b, hT rfl⟩)
    simpa [RingHom.algebraMap_toAlgebra, map_ofNat] using this
  have h2 := h P
  rw [h1, norm_mul, Complex.norm_two] at h2
  have h3 : P₀ b = 0 := norm_eq_zero.1 (by linarith)
  exact hb ((map_eq_zero P₀).1 h3 ▸ isAlgebraic_zero)

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem liesOn_frMap {Z : Comp Xo c} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) (hy : LiesOn Z y) : LiesOn Z z := by
  have e : ptF z = spMap φ.toRingHom ≫ ptF y := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, Category.assoc, ptF, pullback.lift_fst, h.1]
    · rw [ptF, pullback.lift_snd, Category.assoc, ptF, pullback.lift_snd, ← Spec.map_comp]
      congr 1
      ext a
      exact (φ.commutes a).symm
  intro s
  rw [e, Scheme.Hom.comp_apply]
  exact hy _

theorem liesOn_frBor {Z : Comp Xo c} {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y z : FrPt Xo c S}
    (h : FrBor t y z) (hz : LiesOn Z z) : LiesOn Z y := by
  have e : ptF y = ptF z := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, ptF, pullback.lift_fst, h.1]
    · rw [ptF, pullback.lift_snd, ptF, pullback.lift_snd]
  intro s
  rw [e]
  exact hz s

theorem secZ_zero_eq : secZ Xo c 0 = sec Xo c 0 0 := by
  rw [← secZ_nat]
  congr 1
  funext i
  cases i <;> rfl

theorem exists_eq_smul_idem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hF : FnAlgClosed Xo c) {Z : Comp Xo c} {g : Rul Xo c} (hg : g ∈ secZ Xo c 0) (hs : g ∈ suppOn Z) {b : ℝ}
    (hb : ∀ z ∈ framesOn U Z, ‖rdU U g z.1 z.2‖ = b) : ∃ a : c.F, g = a • idem Z := by
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hg hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, ‖toC (P (evC h Z g))‖ = b := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (congrArg norm (one_mul _)).trans (hb _ hz)
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨a, ha⟩ := hF Z _ (isAlgebraic_of_norm_const (K := c.F) (b := evC h Z g) P₀
    fun P => (key P).trans (key P₀).symm)
  refine ⟨a, sub_eq_zero.1 (GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hg (Submodule.smul_mem _ _ hi)) fun Z' => ?_)⟩
  by_cases hZ : Z' = Z
  · subst hZ
    have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
    have h4 := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g ((-a) • idem Z')
      (genFr h Z')
    have h5 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (-a) (idem Z')
      (genFr h Z')
    rw [sub_eq_add_neg, ← neg_smul]
    refine h4.trans ?_
    rw [h5]
    show evC h Z' g + algebraMap _ _ (-a) * evC h Z' (idem Z') = 0
    rw [h3, ← ha, map_neg, mul_one, add_neg_cancel]
  · exact evC_eq_zero h hZ (sub_mem hs (Submodule.smul_mem _ _ (idem_mem_suppOn Z)))

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem ConstSec.exists_eq_smul (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed Xo c) {Z : Comp Xo c}
    {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s t : ConstSec U x Z la δ) :
    ∃ (a : c.F) (ha : a ≠ 0), t = s.smul a ha := by
  have hσ := goodEmb_goodOf c c.F.val.toRingHom
  let u : ConstSec U x Z 0 0 := (t.mul s.symm).copy (add_neg_cancel la) (add_neg_cancel δ)
  obtain ⟨a, ha⟩ := exists_eq_smul_idem (U _) hσ (hU _ hσ) hF (g := u.sig) (exOf_zero (Dw := Dw) ▸ u.sig_mem)
    u.sig_mem_suppOn (b := u.cInf c.F.val.toRingHom) fun z hz => by
      rw [← homN_zero _ x, ← wtOf_zero (Dw := Dw)]; exact u.homN_eq hz
  have ha' : t.sig * s.inv = a • idem Z := ha
  have h : t.sig = a • s.sig :=
    calc t.sig = t.sig * s.inv * s.sig := by
          rw [mul_assoc, mul_comm s.inv, s.mul_inv, mul_comm, t.idem_sig]
      _ = a • s.sig := by rw [ha', smul_mul_assoc, s.idem_sig]
  have h0 : a ≠ 0 := fun h0 => t.sig_ne_zero (by rw [h, h0, zero_smul])
  exact ⟨a, h0, ConstSec.ext h⟩

theorem ConstSec.deg_eq (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed Xo c) {Z : Comp Xo c}
    {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s t : ConstSec U x Z la δ) : t.deg = s.deg := by
  obtain ⟨a, ha, rfl⟩ := ConstSec.exists_eq_smul hU hF s t
  exact ConstSec.deg_smul a ha s

end GlobalTheory.FlatLine
end
end

