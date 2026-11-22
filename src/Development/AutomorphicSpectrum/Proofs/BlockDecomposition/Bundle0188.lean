import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0183
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0178
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffIterateVerschiebung
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcSp

section Witt

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]

theorem coeff_iterate_verschiebung (m : ℕ) (y : WittVector p R) (i : ℕ) (h : i < m) :
    (WittVector.verschiebung^[m] y).coeff i = 0 := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ i =>
      rw [WittVector.verschiebung_coeff_succ]
      exact ih i (by omega)

theorem idem_eq_zero (u : WittVector p R) (hu : u * u = u) (h0 : u.coeff 0 = 0) : u = 0 := by
  have key : ∀ n, ∀ i < n + 1, u.coeff i = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi
      obtain rfl : i = 0 := by omega
      exact h0
    | succ n ih =>
      intro i hi
      by_cases h : i < n + 1
      · exact ih i h
      obtain rfl : i = n + 1 := by omega
      obtain ⟨y, e⟩ : ∃ y, u = WittVector.verschiebung^[n + 1] y := ⟨_, WittVector.eq_iterate_verschiebung ih⟩
      have e2 : u = WittVector.verschiebung^[(n + 1) + (n + 1)]
          (WittVector.frobenius^[n + 1] y * WittVector.frobenius^[n + 1] y) := by
        rw [← WittVector.iterate_verschiebung_mul, ← e, hu]
      rw [e2]
      exact coeff_iterate_verschiebung _ _ _ (by omega)
  ext i
  rw [key i i (by omega)]
  simp

theorem sum_teichmuller {ι : Type} [Fintype ι] (e : ι → R) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller p (e i) = (1 : WittVector p R) := by
  have ho : OrthogonalIdempotents fun i => WittVector.teichmuller p (e i) :=
    { idem := fun i => by
        change _ * _ = _
        rw [← map_mul, (he.idem i).eq]
      ortho := fun i j hij => by
        change _ * _ = _
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hs : IsIdempotentElem (∑ i, WittVector.teichmuller p (e i)) := ho.isIdempotentElem_sum
  have h1 : (1 : WittVector p R) - ∑ i, WittVector.teichmuller p (e i) = 0 := by
    refine idem_eq_zero _ hs.one_sub.eq ?_
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  exact (sub_eq_zero.1 h1).symm

end Witt

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ)

theorem sum_teich {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller l (e i) = (1 : A.W) := by
  rcases subsingleton_or_nontrivial A.A with h | h
  · exact WittVector.ext fun _ => Subsingleton.elim _ _
  · haveI : CharP A.A l := (CharP.charP_iff_prime_eq_zero Fact.out).2 A.natCast_l
    exact sum_teichmuller e he

theorem acr_ext {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) {x y : A.Acr n}
    (h : ∀ i, A.toAcr n (WittVector.teichmuller l (e i)) * x = A.toAcr n (WittVector.teichmuller l (e i)) * y) :
    x = y := by
  have hs : ∑ i, A.toAcr n (WittVector.teichmuller l (e i)) = 1 := by
    rw [← map_sum, sum_teich A e he, map_one]
  calc x = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * x := by rw [hs, one_mul]
    _ = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * y := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => h i
    _ = y := by rw [hs, one_mul]

theorem exists_cast : ∃ c : ZMod (l ^ n) →+* A.Acr n, ∀ a, c a = (a.val : A.Acr n) := by
  haveI : CharP (A.Acr n) (ringChar (A.Acr n)) := ringChar.charP _
  have hd : ringChar (A.Acr n) ∣ l ^ n :=
    (CharP.cast_eq_zero_iff (A.Acr n) (ringChar (A.Acr n)) (l ^ n)).1 (by
      rw [Nat.cast_pow]
      exact A.pow_l_acr n)
  refine ⟨ZMod.castHom hd _, fun a => ?_⟩
  rw [ZMod.castHom_apply, ZMod.natCast_val]

variable {A n}

section Main

variable (hI : LcIdem) (H : RIn l) (hA : A.IsTest)
include hI H hA

theorem exists_isLcA (f : LocallyConstant (SU A) (ZMod (l ^ n))) : ∃ x, IsLcA A n f x := by
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine ⟨∑ a, A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n), fun e' a he' hf => ?_⟩
  have h3 : e' * e a = e' := h2 e' a he' hf
  rw [Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, h3]
  · intro b _ hb
    have h4 : e' * e b = 0 := by
      calc e' * e b = e' * e a * e b := by rw [h3]
        _ = 0 := by rw [mul_assoc, he.ortho hb.symm, mul_zero]
    rw [← mul_assoc, ← map_mul, ← map_mul, h4, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem isLcA_unique {f : LocallyConstant (SU A) (ZMod (l ^ n))} {x y : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n f y) : x = y := by
  obtain ⟨e, he, h1, -⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine acr_ext A n e he fun a => ?_
  have hf : ∀ p : PrimeSpectrum A.Ug, algebraMap A.U A.Ug (A.sharp (e a)) ∉ p.asIdeal → f p = a :=
    fun p hp => (h1 a p).1 hp
  rw [hx (e a) a (he.idem a) hf, hy (e a) a (he.idem a) hf]

theorem isLcA_one : IsLcA A n 1 1 := by
  obtain ⟨c, hc⟩ := exists_cast A n
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) 1
  intro e' a he' hf
  by_cases ha : a = 1
  · subst ha
    rw [← hc, map_one]
  · have h3 : e' * e a = e' := h2 e' a he' hf
    have h4 : e' * e 1 = e' := h2 e' 1 he' fun _ _ => rfl
    have h5 : e' = 0 := by
      calc e' = e' * e 1 * e a := by rw [h4, h3]
        _ = 0 := by rw [mul_assoc, he.ortho (Ne.symm ha), mul_zero]
    rw [h5, WittVector.teichmuller_zero, map_zero, zero_mul, zero_mul]

theorem exists_pair (f g : LocallyConstant (SU A) (ZMod (l ^ n))) :
    ∃ e : ZMod (l ^ n) × ZMod (l ^ n) → A.A, CompleteOrthogonalIdempotents e ∧
      ∀ (ab : ZMod (l ^ n) × ZMod (l ^ n)) (p : PrimeSpectrum A.Ug),
        algebraMap A.U A.Ug (A.sharp (e ab)) ∉ p.asIdeal → f p = ab.1 ∧ g p = ab.2 := by
  let h : LocallyConstant (SU A) (ZMod (l ^ n) × ZMod (l ^ n)) :=
    ⟨fun p => (f p, g p), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  obtain ⟨e, he, h1, -⟩ := hI l H A hA _ h
  refine ⟨e, he, fun ab p hp => ?_⟩
  have h2 : (f p, g p) = ab := (h1 ab p).1 hp
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

theorem isLcA_add {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f + g) z) : z = x + y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 + ab.2) (he.idem ab) fun p hp => by
    change f p + g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  rw [h3, mul_add, h1, h2, ← hc, ← hc, ← hc, map_add, mul_add]

theorem isLcA_mul {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f * g) z) : z = x * y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 * ab.2) (he.idem ab) fun p hp => by
    change f p * g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  have ht : A.toAcr n (WittVector.teichmuller l (e ab)) * A.toAcr n (WittVector.teichmuller l (e ab)) =
      A.toAcr n (WittVector.teichmuller l (e ab)) := by
    rw [← map_mul, ← map_mul, (he.idem ab).eq]
  rw [← hc] at h1 h2 h3
  calc _ = A.toAcr n (WittVector.teichmuller l (e ab)) * (c ab.1 * c ab.2) := by rw [h3, map_mul]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.1) * (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.2) := by
      rw [mul_mul_mul_comm, ht]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * x) * (A.toAcr n (WittVector.teichmuller l (e ab)) * y) := by
      rw [h1, h2]
    _ = _ := by rw [mul_mul_mul_comm, ht]

end Main

theorem lcSpec_of_lcIdem : CrystallineSemistableComparison.E.LcIdem → CrystallineSemistableComparison.E.LcSpec := by
  intro hI l _ H A hA n
  have P : ∃ κ : LocallyConstant (SU A) (ZMod (l ^ n)) →+ A.Acr n, ∀ f, IsLcA A n f (κ f) := by
    choose k hk using exists_isLcA (n := n) hI H hA
    exact ⟨AddMonoidHom.mk' k fun f g => isLcA_add hI H hA (hk f) (hk g) (hk (f + g)), hk⟩
  have S : ∀ f, IsLcA A n f (lcA A n f) := pick_spec P
  refine ⟨S, isLcA_unique hI H hA (S 1) (isLcA_one hI H hA),
    fun f g => isLcA_mul hI H hA (S f) (S g) (S (f * g)), fun f e he h => ?_⟩
  refine acr_ext A n e he fun a => ?_
  rw [S f (e a) a (he.idem a) (h a), Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, (he.idem a).eq]
  · intro b _ hb
    rw [← mul_assoc, ← map_mul, ← map_mul, he.ortho hb.symm, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ a) h'

end GlobalTheory.CompanionTheory.LcSp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturated
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

theorem Fil0_succ_le {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.Fil0 (r + 1) ≤ A.Fil0 r :=
  Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

theorem crystalline_filtration_l_saturated : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0),
    (l : A.Acr0) * z ∈ A.Fil0 r → z ∈ A.Fil0 r := by
  intro l _ A r
  induction r with
  | zero =>
    intro z _
    rw [(GlobalTheory.T.crystalline_filtration_multiplicative A).1]
    exact Submodule.mem_top
  | succ r ih =>
    intro z hz
    have hzr : z ∈ A.Fil0 r := ih z (Fil0_succ_le A r hz)
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.crystalline_graded_pieces_description A r
    obtain ⟨w, hw⟩ := h1 z hzr
    have hlw : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r ∈ A.Fil0 (r + 1) := by
      have e : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r =
          (l : A.Acr0) * z - (l : A.Acr0) * (z - algebraMap A.W A.Acr0 w * A.dxi0 r) := by
        rw [map_mul, map_natCast]; ring
      rw [e]
      exact sub_mem hz (Ideal.mul_mem_left _ _ hw)
    have hmem : (l : A.W) * w ∈ Ideal.span {A.xi} := (h2 _).1 hlw
    have hth : (l : A.U) * A.th w = 0 := by
      rw [← map_natCast A.th, ← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
    have hth0 : A.th w = 0 :=
      (mem_nonZeroDivisors_iff_left.1 (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).1) _ hth
    have hwx : w ∈ Ideal.span {A.xi} := Ideal.Quotient.eq_zero_iff_mem.1 hth0
    have := add_mem hw ((h2 w).2 hwx)
    simpa using this

end GlobalTheory.CompanionTheory.PerfFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCoordNeZero
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Relevant

theorem exists_coord_ne_zero :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Ω _ _ y D hP k
  obtain ⟨i, hi⟩ := hP.2.1.2.2 k
  exact ⟨i, fun h0 => hi (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.X_mem_of_eq_zero h0)⟩

end GlobalTheory.CompanionTheory.Ar.Relevant
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIdem
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TiltIdem

variable {B R : Type} [CommRing B] [CommRing R]

theorem idem_eq (i : B →* R)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {x y : B} (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
    (h : ∀ p : PrimeSpectrum R, i x ∉ p.asIdeal ↔ i y ∉ p.asIdeal) : x = y := by
  have hix : IsIdempotentElem (i x) := by
    change i x * i x = i x
    rw [← map_mul, hx.eq]
  have hiy : IsIdempotentElem (i y) := by
    change i y * i y = i y
    rw [← map_mul, hy.eq]
  have hb : PrimeSpectrum.basicOpen (i x) = PrimeSpectrum.basicOpen (i y) := by
    ext p
    exact h p
  have e : i x = i y := PrimeSpectrum.basicOpen_injOn_isIdempotentElem hix hiy hb
  exact (hidem (i y) hiy).unique ⟨hx, e⟩ ⟨hy, rfl⟩

theorem exists_idem (i : B →* R) (h0 : i 0 = 0)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {ι : Type} [Fintype ι] (f : LocallyConstant (PrimeSpectrum R) ι) :
    ∃ e : ι → B, CompleteOrthogonalIdempotents e ∧
      (∀ (a : ι) (p : PrimeSpectrum R), i (e a) ∉ p.asIdeal ↔ f p = a) ∧
      ∀ (e' : B) (a : ι), IsIdempotentElem e' →
        (∀ p : PrimeSpectrum R, i e' ∉ p.asIdeal → f p = a) → e' * e a = e' := by
  classical
  have hfib : ∀ a : ι, ∃ e : B, IsIdempotentElem e ∧
      ∀ p : PrimeSpectrum R, i e ∉ p.asIdeal ↔ f p = a := by
    intro a
    have hc : IsClopen (f ⁻¹' {a}) := f.isLocallyConstant.isClopen_fiber a
    obtain ⟨ε, hε, hs⟩ := PrimeSpectrum.isClopen_iff.1 hc
    obtain ⟨e₀, ⟨he₀, rfl⟩, -⟩ := hidem ε hε
    refine ⟨e₀, he₀, fun p => ?_⟩
    have : p ∈ f ⁻¹' {a} ↔ p ∈ PrimeSpectrum.basicOpen (i e₀) := by rw [hs]; rfl
    exact this.symm
  choose e he hp using hfib
  have hnot0 : ∀ p : PrimeSpectrum R, ¬ (i 0 ∉ p.asIdeal) := fun p h => h (by rw [h0]; exact p.asIdeal.zero_mem)
  have hmul : ∀ (x y : B) (p : PrimeSpectrum R), i (x * y) ∉ p.asIdeal ↔ i x ∉ p.asIdeal ∧ i y ∉ p.asIdeal := by
    intro x y p
    rw [map_mul, p.isPrime.mul_mem_iff_mem_or_mem]
    tauto
  have hort : OrthogonalIdempotents e := by
    refine ⟨he, fun a b hab => ?_⟩
    refine idem_eq i hidem ((he a).mul (he b)) IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    obtain ⟨h1, h2⟩ := (hmul _ _ p).1 h
    exact hab (((hp a p).1 h1).symm.trans ((hp b p).1 h2))
  have hsum : IsIdempotentElem (∑ a, e a) := hort.isIdempotentElem_sum
  have hc : IsIdempotentElem (1 - ∑ a, e a) := hsum.one_sub
  have hce : ∀ a, (1 - ∑ b, e b) * e a = 0 := by
    intro a
    rw [sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single a, (he a).eq, sub_self]
    · exact fun b _ hb => hort.ortho hb
    · exact fun h => absurd (Finset.mem_univ a) h
  have hone : 1 - ∑ a, e a = 0 := by
    refine idem_eq i hidem hc IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    have h1 : i (e (f p)) ∉ p.asIdeal := (hp (f p) p).2 rfl
    have h2 := (hmul _ _ p).2 ⟨h, h1⟩
    rw [hce] at h2
    exact hnot0 p h2
  refine ⟨e, ⟨hort, (sub_eq_zero.1 hone).symm⟩, hp, fun e' a he' h => ?_⟩
  refine idem_eq i hidem (he'.mul (he a)) he' fun p => ?_
  rw [hmul]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', (hp a p).2 (h p h')⟩⟩

theorem sharp_zero' {l : ℕ} [Fact l.Prime] (A : PAlg l) : A.sharp 0 = 0 := by
  change A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

theorem lcIdem : CrystallineSemistableComparison.E.LcIdem := by
  intro l _ H A hA ι _ f
  let i : A.A →* A.Ug := (algebraMap A.U A.Ug : A.U →* A.Ug).comp A.sharp
  have h0 : i 0 = 0 := by
    change algebraMap A.U A.Ug (A.sharp 0) = 0
    rw [sharp_zero', map_zero]
  let f' : LocallyConstant (PrimeSpectrum A.Ug) ι := ⟨f, f.isLocallyConstant⟩
  exact exists_idem i h0 (H.idem A hA) f'

end GlobalTheory.CompanionTheory.TiltIdem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.RootsC

variable {l : ℕ} [hl : Fact l.Prime]

theorem seq_add_pow (m d : ℕ) : rootSeq l (m + d) ^ l ^ d = rootSeq l m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, pow_succ', pow_mul, GroundTheory.PAdicHodge.rootSeq_succ_pow, ih]

theorem seq_primitive (n : ℕ) : IsPrimitiveRoot (rootSeq l n) (l ^ n) := by
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    simpa using (GroundTheory.PAdicHodge.rootSeq_pow (p := l) 0)
  | succ k =>
    have h1 : ¬ rootSeq l (k + 1) ^ l ^ k = 1 := by
      rw [Nat.add_comm, seq_add_pow]
      exact GroundTheory.PAdicHodge.rootSeq_one_ne_one
    have h2 := orderOf_eq_prime_pow h1 (GroundTheory.PAdicHodge.rootSeq_pow (p := l) (k + 1))
    rw [← h2]
    exact IsPrimitiveRoot.orderOf _

theorem exists_primitive_cl (n : ℕ) : ∃ η : PadicAlgCl l, IsPrimitiveRoot η (l ^ n) := by
  have hq : (l ^ n : ℕ) ≠ 0 := pow_ne_zero n hl.out.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : PadicAlgCl l) := ⟨by exact_mod_cast hq⟩
  have hdeg : (Polynomial.cyclotomic (l ^ n) (PadicAlgCl l)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have ht : 0 < Nat.totient (l ^ n) := Nat.totient_pos.2 (Nat.pos_of_ne_zero hq)
    exact_mod_cast ht.ne'
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨η, Polynomial.isRoot_cyclotomic_iff.1 hη⟩

theorem exists_lift (n : ℕ) :
    ∃ ρ : PadicAlgCl l, IsPrimitiveRoot ρ (l ^ n) ∧ clToC l ρ = rootSeq l n := by
  obtain ⟨η, hη⟩ := exists_primitive_cl (l := l) n
  have hinj : Function.Injective (clToC l) := (clToC l).injective
  have hη' : IsPrimitiveRoot (clToC l η) (l ^ n) :=
    (IsPrimitiveRoot.map_iff_of_injective hinj).2 hη
  obtain ⟨i, -, hi⟩ := hη'.eq_pow_of_pow_eq_one (GroundTheory.PAdicHodge.rootSeq_pow (p := l) n)
  refine ⟨η ^ i, ?_, by rw [map_pow, hi]⟩
  rw [← IsPrimitiveRoot.map_iff_of_injective hinj, map_pow, hi]
  exact seq_primitive n

theorem prim_of_primitive {q : ℕ} (hq : q ≠ 0) {F : Type} [Field F] [CharZero F] {ρ : F}
    (h : IsPrimitiveRoot ρ q) :
    IsUnit ((q : ℕ) : F) ∧ Polynomial.aeval ρ (Polynomial.cyclotomic q ℤ) = 0 := by
  refine ⟨isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hq), ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact h.isRoot_cyclotomic (Nat.pos_of_ne_zero hq)

theorem rootsEx : CrystallineSemistableComparison.E.RootsEx := by
  intro l _
  choose ρ hρ using fun n => exists_lift (l := l) n
  exact ⟨⟨fun n => Subtype.mk (ρ n)
      (prim_of_primitive (pow_ne_zero n (Fact.out : l.Prime).ne_zero) (hρ n).1),
    fun n => (hρ n).2⟩⟩

end GlobalTheory.CompanionTheory.RootsC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIdempotentLiftTiltStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_idempotent_lift_tilt : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U), IsIdempotentElem e → ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp | exact GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankChartLatQMono
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.ChartSections

theorem finrank_chartLatQ_mono : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (b b' : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → b ≤ b' →
    FiniteDimensional ℚ (chartLatQ y b' 1) →
    Module.finrank ℚ (chartLatQ y b 1) ≤ Module.finrank ℚ (chartLatQ y b' 1) := by
  intro K _ ι _ Ω _ _ y b b' hy hb hfd
  choose j hj using hy
  obtain ⟨n, hn⟩ : ∃ n : K → ℕ, ∀ k, (n k : ℤ) = b' k - b k :=
    ⟨fun k => (b' k - b k).toNat, fun k => Int.toNat_of_nonneg (sub_nonneg.2 (hb k))⟩
  have hu0 : (∏ k, y ⟨k, j k⟩ ^ n k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hj k)
  have hmem : ∀ s ∈ chartLatQ y b 1, s * ∏ k, y ⟨k, j k⟩ ^ n k ∈ chartLatQ y b' 1 := by
    intro s hs c hc
    have h1 : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) ∈ chartRingQ y c := hs c hc
    have hq : ∀ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ ∈ chartRingQ y c :=
      fun k => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
    have h2 : ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ n k ∈ chartRingQ y c :=
      prod_mem fun k _ => pow_mem (hq k) _
    have heq : s * (∏ k, y ⟨k, j k⟩ ^ n k) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) * ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ n k := by
      rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      have hck := hc k
      have hnk := hn k
      have hz : y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) =
          y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) * (y ⟨k, c k⟩ ^ n k)⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hck]
        congr 1
        simp only [Nat.cast_one, one_mul]
        omega
      rw [hz, div_pow, div_eq_mul_inv]
      ring
    show s * (∏ k, y ⟨k, j k⟩ ^ n k) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) ∈ chartRingQ y c
    rw [heq]
    exact mul_mem h1 h2
  let f : chartLatQ y b 1 →ₗ[ℚ] chartLatQ y b' 1 :=
    { toFun := fun s => ⟨s.1 * ∏ k, y ⟨k, j k⟩ ^ n k, hmem s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r s => Subtype.ext (smul_mul_assoc _ _ _) }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun s t hst => ?_
  exact Subtype.ext (mul_right_cancel₀ hu0 (congrArg Subtype.val hst))

end GlobalTheory.CompanionTheory.ChartSections
end

