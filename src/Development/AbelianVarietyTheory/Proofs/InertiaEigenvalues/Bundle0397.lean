import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowPlacesSatisfyRowHypothesisAtQAndD
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.RowBoundB

open Module

theorem good_one {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {s : ℕ} (hl : l ≠ 2) (h : Good K s LL)
    (hK : K.1 ≤ Ks K 1) : Good K 1 LL := by
  obtain ⟨hs, -, -, hτ⟩ := h
  refine ⟨le_rfl, fun h2 => absurd h2 hl, hK, fun τ x => ?_⟩
  have hle : Ks K 1 ≤ Ks K s := by
    refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
    intro y hy
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [pow_add, pow_mul, hy, one_pow]
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ_[l]) (L := ↥(Ks K 1))
    (M := Om l) (E := Om l) τ
  have := hτ (φ.comp (Ks K s).val) ⟨x.1, hle x.2⟩
  rw [← hφ]
  exact this

theorem jump_windows (η Sc b : ℝ) (t : ℕ) (hη : 0 < η) (hS : 0 < Sc) (ht : 1 ≤ (t : ℝ))
    (hpar : Sc + η + t + 2 ≤ b) (s : ℤ) (Jc Jl : Finset ℤ)
    (h1 : η + t + 1 < (s : ℝ)) (h2 : (s : ℝ) ≤ b + η + t + 1)
    (hl : ∀ a ∈ Jl, ((-η + ((t : ℝ) - 1) / 2 ≤ (a : ℝ) ∧ a ≤ -2) ∨
            ((t : ℤ) + 1 ≤ a ∧ (a : ℝ) ≤ η + ((t : ℝ) - 1) / 2)))
    (hc : (∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + Sc) ∨ (∀ a ∈ Jc, -((s : ℝ) + Sc) ≤ a ∧ a ≤ -s)) :
    ∃ (up : Bool) (bτ : ℕ), ⌊η⌋₊ + t < bτ ∧
      (∀ a : ℤ, (-a - 1 ∈ Jc ∨ -a - 1 ∈ Jl ∨ (0 ≤ -a - 1 ∧ -a - 1 < t)) →
        a ∈ ElementDenominator.deep up bτ ⌊Sc⌋₊ ∪ Set.Icc (-((⌊η⌋₊ + t : ℕ) : ℤ)) ((⌊η⌋₊ + t : ℕ) : ℤ) ∧
        a ∈ Set.Icc (-((⌊2 * b⌋₊ : ℕ) : ℤ)) ((⌊2 * b⌋₊ : ℕ) : ℤ)) ∧
      ∀ a ∈ Finset.Icc (-((⌊η⌋₊ + t : ℕ) : ℤ)) ((⌊η⌋₊ + t : ℕ) : ℤ), -a - 1 ∉ Jc := by
  have key : ∀ (x : ℝ) (n : ℤ), 0 ≤ x → (n : ℝ) ≤ x → n ≤ ((⌊x⌋₊ : ℕ) : ℤ) := by
    intro x n hx hn
    rw [Int.natCast_floor_eq_floor hx]
    exact Int.le_floor.2 hn
  have e1 : ((⌊η⌋₊ : ℕ) : ℝ) ≤ η := Nat.floor_le hη.le
  have e2 : ((⌊Sc⌋₊ : ℕ) : ℝ) ≤ Sc := Nat.floor_le hS.le
  have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have hs1 : ((⌊η⌋₊ : ℕ) : ℤ) + t + 1 < s := by
    have : (((⌊η⌋₊ : ℕ) : ℤ) : ℝ) + ((t : ℤ) : ℝ) + 1 < (s : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hb : s + 1 + ((⌊Sc⌋₊ : ℕ) : ℤ) ≤ ((⌊2 * b⌋₊ : ℕ) : ℤ) := by
    apply key _ _ (by linarith)
    push_cast; linarith
  have hlow : ∀ a : ℤ, -a - 1 ∈ Jl → -(((⌊η⌋₊ : ℕ) : ℤ) + t) ≤ a ∧ a ≤ ((⌊η⌋₊ : ℕ) : ℤ) + t := by
    intro a ha
    rcases hl _ ha with ⟨p, q⟩ | ⟨p, q⟩
    · have : a ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
        apply key _ _ hη.le
        push_cast at p; linarith
      omega
    · have : -a - t ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
        apply key _ _ hη.le
        push_cast at q ⊢; linarith
      omega
  rcases hc with hc | hc
  · have hc' : ∀ a : ℤ, -a - 1 ∈ Jc → s ≤ -a - 1 ∧ -a - 1 - s ≤ ((⌊Sc⌋₊ : ℕ) : ℤ) := by
      intro a ha
      obtain ⟨p, q⟩ := hc _ ha
      refine ⟨p, key _ _ hS.le ?_⟩
      push_cast at q ⊢; linarith
    refine ⟨false, (s + 1).toNat, by omega, fun a ha => ?_, fun a ha hj => ?_⟩
    · simp only [ElementDenominator.deep, Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc]
      rcases ha with ha | ha | ha
      · have := hc' a ha
        omega
      · have := hlow a ha
        omega
      · omega
    · have := hc' a hj
      rw [Finset.mem_Icc] at ha
      omega
  · have hc' : ∀ a : ℤ, -a - 1 ∈ Jc → -a - 1 ≤ -s ∧ a + 1 - s ≤ ((⌊Sc⌋₊ : ℕ) : ℤ) := by
      intro a ha
      obtain ⟨p, q⟩ := hc _ ha
      refine ⟨q, key _ _ hS.le ?_⟩
      push_cast at p ⊢; linarith
    refine ⟨true, (s - 1).toNat, by omega, fun a ha => ?_, fun a ha hj => ?_⟩
    · simp only [ElementDenominator.deep, if_true, Set.mem_union, Set.mem_Icc]
      rcases ha with ha | ha | ha
      · have := hc' a ha
        omega
      · have := hlow a ha
        omega
      · omega
    · have := hc' a hj
      rw [Finset.mem_Icc] at ha
      omega

theorem sum_le_card (I Jl : Finset ℤ) (f : ℤ → ℤ) (h1 : ∀ a ∈ I, f a ≤ 1)
    (h0 : ∀ a ∈ I, -a - 1 ∉ Jl → f a = 0) : ∑ a ∈ I, f a ≤ Jl.card := by
  classical
  have e : ∑ a ∈ I, f a ≤ ∑ a ∈ I, (if -a - 1 ∈ Jl then (1 : ℤ) else 0) := by
    refine Finset.sum_le_sum fun a ha => ?_
    split_ifs with h
    · exact h1 a ha
    · exact (h0 a ha h).le
  refine e.trans ?_
  rw [Finset.sum_boole]
  have : (I.filter fun a => -a - 1 ∈ Jl).card ≤ Jl.card := by
    refine Finset.card_le_card_of_injOn (fun a => -a - 1) (fun a ha => (Finset.mem_filter.1 ha).2) ?_
    intro a _ b _ hab
    simp only at hab
    omega
  exact_mod_cast this

theorem boundA_le (CA η Sc b : ℝ) (l n r t m f : ℕ) (hl : 2 ≤ l) (hη : 0 < η) (hS : 0 < Sc) (hb : 1 ≤ b)
    (hf : f = n * 2) :
    ElementDenominator.boundA CA l n 2 r ⌊Sc⌋₊ (⌊η⌋₊ + t) m ⌊2 * b⌋₊ ≤
      max CA 0 * (((f : ℕ) + 1 : ℝ) * (r : ℝ) * (4 * b / (l : ℝ) + 2 * Sc + 2 * Real.logb (l : ℝ) (2 * b) + 1 + η + (t : ℝ)) + 3 * ((f : ℕ) : ℝ) * (m : ℝ) * (2 * b + 1)) := by
  have e1 : ((⌊η⌋₊ : ℕ) : ℝ) ≤ η := Nat.floor_le hη.le
  have e2 : ((⌊Sc⌋₊ : ℕ) : ℝ) ≤ Sc := Nat.floor_le hS.le
  have e3 : ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ 2 * b := Nat.floor_le (by linarith)
  have e4 : (1 : ℝ) ≤ ((⌊2 * b⌋₊ : ℕ) : ℝ) := by
    have : 1 ≤ ⌊2 * b⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hl' : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have e5 : 0 ≤ Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) := Real.logb_nonneg hl' e4
  have e6 : Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ Real.logb (l : ℝ) (2 * b) :=
    Real.logb_le_logb_of_le hl' (by linarith) e3
  have e7 : 2 * ((⌊2 * b⌋₊ : ℕ) : ℝ) / (l : ℝ) ≤ 4 * b / (l : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hQ : ElementDenominator.boundA CA l n 2 r ⌊Sc⌋₊ (⌊η⌋₊ + t) m ⌊2 * b⌋₊ =
      CA * (((f : ℕ) + 1 : ℝ) * (r : ℝ) * (2 * ((⌊2 * b⌋₊ : ℕ) : ℝ) / (l : ℝ) + 2 * ((⌊Sc⌋₊ : ℕ) : ℝ) +
        2 * Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) + 1 + ((⌊η⌋₊ : ℕ) : ℝ) + (t : ℝ)) +
        3 * ((f : ℕ) : ℝ) * (m : ℝ) * (((⌊2 * b⌋₊ : ℕ) : ℝ) + 1)) := by
    simp only [ElementDenominator.boundA, hf]
    push_cast
    ring
  rw [hQ]
  refine (mul_le_mul_of_nonneg_right (le_max_left CA 0) (by positivity)).trans ?_
  gcongr

theorem rowAt_of_thmA {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (CA : ℝ)
    (hT : ElementDenominator.thmA P K LL CA) (he : finrank ↥(K0 K) ↥K.1 = 2) {ι : Type} {k r : ℕ}
    (Ms : ι → ↥(GK K) → Matrix (Fin k) (Fin k) ↥LL.1) (M2 : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1)
    (S η m h : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) (q : ℚ)
    (h1 : ∀ (V1 : Type) [AddCommGroup V1] [Module ↥LL.1 V1] [Module ℚ_[l] V1]
          [IsScalarTower ℚ_[l] ↥LL.1 V1] [FiniteDimensional ↥LL.1 V1]
          (ρ1 : Representation ↥LL.1 ↥(GK K) V1), IsSubOfSums ρ1 Ms → IsCrys (P.PD K) ρ1 ∧
          ∀ τ a, IsJumpV (P.PD K) ρ1 τ a →
            a ∈ ElementDenominator.deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η ∧ a ∈ Set.Icc (-(h : ℤ)) h)
    (h2 : IsCrys (P.PD K) (matRep M2)) (hb : ∀ τ, η < b τ)
    (hsum : ∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) (matRep M2) τ a ≤ m)
    (hq : ElementDenominator.boundA CA l (finrank ℚ_[l] ↥(K0 K)) 2 r S η m h ≤ q) :
    RowAt (P.PD K) (O := ↥(OL LL)) Ms ⇑M2 q := by
  intro V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 T2 hc2 hmat V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 T1 hc1 hsub F hFo
  obtain ⟨c1, c2⟩ := h1 V1 ρ1 hsub
  obtain ⟨e, heg, -⟩ := hmat
  have he' : ∀ g v, e (ρ2 g v) = matRep M2 g (e v) := by
    intro g v
    rw [heg]
    simp [matRep, Matrix.toLinAlgEquiv'_apply]
  have hr : finrank ↥LL.1 V2 = r := by simpa using e.finrank_eq
  have hs2 : ∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) ρ2 τ a ≤ m := by
    intro τ
    simp only [GlobalTheory.HTW.Rec.multV_eq_of_equiv _ e he']
    exact hsum τ
  obtain ⟨mm, k, hm, hk, hle⟩ := hT { V := V1, ρ := ρ1, cont := hc1, L := T1 }
    { V := V2, ρ := ρ2, cont := hc2, L := T2 } F r S η m h up b c1
    (GlobalTheory.HTW.Rec.isCrys_of_equiv _ e he' h2) hFo hr
    (fun τ a ha => (c2 τ a ha).1) hb hs2 (fun τ a ha => (c2 τ a ha).2) (Or.inl he)
  refine ⟨mm, k, hm, hk, ?_⟩
  rw [he] at hle
  have h3 := hle.trans (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg k))
  exact_mod_cast h3

theorem row_bound : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := by
  intro D r ρ large₂ ep CA h0 h1 hA hJ hF _ _ hLit hPar i hi π hπ dc
  refine ⟨fun w => ((⌈max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1))⌉ : ℤ) : ℚ), ?_, fun w _ => ?_⟩
  swap
  · rw [Rat.cast_intCast]
    exact (Int.ceil_lt_add_one _).le
  intro w hw _ C hC
  have hl4 : D.nd.l i % 4 = 3 := (h1 (D.nd.l i) (by simpa using hi.1.1)).1
  have hl2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨-, hK1, he, -⟩ := h0 i hi.1.1 w hw
  have hG : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 hK1
  have hdeg : locDeg D.host.E w = finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) * 2 := by
    have h := ((hLit i hi).2.2.1 w hw).2.2
    unfold Br.DegW at h
    rw [← h, ← he]
    exact (Module.finrank_mul_finrank _ _ _).symm
  have hT := hA (D.nd.l i) hl2 _ _ hG
  have hη := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have ht := large₂.t_win.1
  have hb : 1 ≤ large₂.sc.b := by unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hPar; linarith
  choose s Jc Jl j1 j2 _ j4 j5 j6 _ _ j9 using hJ i hi w hw C
  choose up bτ w1 w2 w3 using fun τ => jump_windows large₂.etaSz large₂.Sc large₂.sc.b D.R.t hη hS ht hPar (s τ) (Jc τ) (Jl τ)
    (j1 τ) (j2 τ) (fun a ha => (j5 τ a ha).1) (j6 τ)
  obtain ⟨f1, f2⟩ := hF i hi w hw C
  obtain ⟨g1, g2⟩ := f2 π hπ
  have hbd := boundA_le CA large₂.etaSz large₂.Sc large₂.sc.b (D.nd.l i) _ D.R.r D.R.t D.R.m _ (by omega) hη hS hb hdeg
  refine rowAt_of_thmA (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL CA hT he _ _
    ⌊large₂.Sc⌋₊ (⌊large₂.etaSz⌋₊ + D.R.t) D.R.m ⌊2 * large₂.sc.b⌋₊ up bτ _ ?_ g1 w1 ?_ ?_
  · intro V1 _ _ _ _ _ ρ1 hsub
    obtain ⟨c1, c2⟩ := f1 V1 ρ1 hsub
    refine ⟨c1, fun τ a ha => ?_⟩
    obtain ⟨x, hx⟩ := c2 τ a ha
    exact w2 τ a ((j9 τ x _).1 hx)
  · intro τ
    rw [← j4 τ]
    apply sum_le_card
    · intro a _
      by_cases hh : (IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ)))
      · exact ((g2 τ a).1 hh).le
      · exact ((g2 τ a).2 hh).le.trans zero_le_one
    · intro a ha hn
      refine (g2 τ a).2 ?_
      rintro ⟨p, q⟩
      rcases (j9 τ π _).1 p with h | h | h
      · exact w3 τ a ha h
      · exact hn h
      · exact q h
  · rw [Rat.cast_intCast]
    exact hbd.trans (Int.le_ceil _)

end GlobalTheory.RowBoundB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeOfConjDualCharpoly
section
noncomputable section

namespace GlobalTheory.LatticeSelfDual

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.AntiRamConj

theorem trace_eq_of_charpoly_eq' {K : Type} [CommRing K] [Nontrivial K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly = B.charpoly) : A.trace = B.trace := by
  rcases n with _ | n
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

def conjC (D : D7) : Gen.GE D.nd →* Gen.GE D.nd where
  toFun := conjAut D.ntw.cc (fun x => ⟨_, cc_symm_algebraMap_host D x⟩)
  map_one' := by ext x; simp [conjAut_apply]
  map_mul' g h := by ext x; simp [conjAut_apply]

theorem conjC_apply (D : D7) (g : Gen.GE D.nd) (x : D.nd.Om) :
    conjC D g x = D.ntw.cc (g (D.ntw.cc.symm x)) := rfl

section
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem tmat_one (i : X.Tw) (s : X.Sig i) : Tmat i s 1 = 1 := by
  rw [← Tgl_coe, map_one, Units.val_one]

theorem tmat_mul (i : X.Tw) (s : X.Sig i) (g h : Gen.GE N) : Tmat i s (g * h) = Tmat i s g * Tmat i s h := by
  rw [← Tgl_coe, ← Tgl_coe, ← Tgl_coe, map_mul, Units.val_mul]

def twistHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun g := (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g
  map_one' := by simp [tmat_one]
  map_mul' g h := by
    rw [tmat_mul, map_mul, Units.val_mul, mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

def dualHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun g := Tdual i s g
  map_one' := by simp [Tdual, tmat_one]
  map_mul' g h := by
    simp only [Tdual]
    rw [tmat_mul, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]

theorem span_twist (i : X.Tw) (s : X.Sig i)
    (h : Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField (X.O0 i))
      (Set.range fun g => (twistHom i s g).map (IsLocalRing.residue (X.O0 i))) = ⊤ := by
  rw [eq_top_iff, ← h, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  let u : (X.O0 i)ˣ := (eps0 X i g ^ D.R.t * (chiS i s g)⁻¹)⁻¹
  have e : rbar X i s g = IsLocalRing.residue (X.O0 i) (u : X.O0 i) •
      (twistHom i s g).map (IsLocalRing.residue (X.O0 i)) := by
    have e2 : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) =
        (u : X.O0 i) • twistHom i s g := by
      show _ = (u : X.O0 i) • ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g)
      rw [Tmat, smul_smul, smul_smul, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul]
    rw [rbar, e2]
    ext a b
    simp
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end

theorem selfDual_of_charDual : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → CharDual i s → SelfDual i s := by
  intro D i s h2 hc
  have : CharZero (FractionRing (D.ntw.O0 i)) := charZero_of_injective_ringHom (D.ntw.emb0 i).injective
  have : CharZero (D.ntw.O0 i) :=
    ((algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero_iff (IsFractionRing.injective _ _)).2 inferInstance
  obtain ⟨U, hU⟩ := GlobalTheory.TraceConj.exists_gl_conj_of_trace_eq (D.ntw.O0 i) (Gen.GE D.nd) D.R.r (twistHom i s).toHomUnits
    ((dualHom i s).comp (conjC D)).toHomUnits (span_twist i s h2.1)
    (fun g => trace_eq_of_charpoly_eq' (hc g (conjC D g) (conjC_apply D g)))
  refine ⟨U, fun g g' hg => ?_⟩
  obtain rfl : g' = conjC D g := by ext x; rw [hg, conjC_apply]
  have := congrArg Units.val (eq_mul_inv_of_mul_eq (hU g))
  rw [Units.val_mul, Units.val_mul] at this
  exact this

end GlobalTheory.LatticeSelfDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerPresentationMatrixOfGaloisCohomology
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelFun

theorem oneMatrix_of_galoisCohomology :
    Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness →
    LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar →
    UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching →
    ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
      (bkP : BKPh X), ThmS bkP := by
  intro _ hPT hCD _ hLF hLT hLE hGF hGE _ hadm D N X bkP
  refine GlobalTheory.T.selmer_theorem_of_local_components GlobalTheory.T.torsion_left_exact_functor_kernel_square_matrix D N X bkP ?_
  intro i s Λ _ _ _ κ Q hS
  have hN := GlobalTheory.T.noGaloisInvariantsTorsionCoeff_of_selmerSetup D N X bkP i s Λ κ Q hS
  have hU := GlobalTheory.T.localConditionAboveLSaturated_of_selmerSetup hLF hLT hLE hadm D N X bkP i s Λ κ Q hS
  have hC := GlobalTheory.T.local_count_of_setup hLF hLT hLE hadm D N X bkP i s Λ κ Q hS
  exact ⟨GlobalTheory.SelFun.selMaps D N X bkP i s Λ κ Q,
    GlobalTheory.T.selmer_functor_left_exact_torsion_coefficients D N X bkP i s Λ κ Q hS hN hU,
    GlobalTheory.SelFun.Colim.selColim D N X bkP i s Λ κ Q hS hN hU,
    GlobalTheory.T.selmerObstruction_le_residualSelmer_simpleExtension hPT hCD hLF hLT hLE hGF hGE D N X bkP i s Λ κ Q hS hN hU hC⟩

end GlobalTheory.SelFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemiBCInjectiveOfInjective
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_injective_of_injective : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B),
    Function.Injective f → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N),
    SemiBC u → Function.Injective u := by
  intro A B _ _ f hf M _ _ _ _ N _ _ u h
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let v : M →ₛₗ[f] (Fin n → B) :=
    { toFun := fun x i => f (s x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  rw [← LinearMap.ker_eq_bot (τ₁₂ := f), LinearMap.ker_eq_bot']
  intro x hx
  have h1 : v x = 0 := by rw [← hS, hx, map_zero]
  have h2 : s x = 0 := by
    funext i
    apply hf
    rw [Pi.zero_apply, map_zero]
    exact congrFun h1 i
  have h3 : x = p (s x) := by
    rw [← LinearMap.comp_apply, hps, LinearMap.id_apply]
  rw [h3, h2, map_zero]

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimplificationOfLinearEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem isSemisimplificationOf_of_equiv : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {W' : Type} [AddCommGroup W'] [Module k W'] [FiniteDimensional k W'] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ W') (ρ : Representation k Γ V) (e : W ≃ₗ[k] W'), (∀ g v, e (s g v) = s' g (e v)) → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s' ρ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  intro k Γ _ _ W _ _ _ W' _ _ _ V _ _ _ s s' ρ e he h
  obtain ⟨hss, m, Ws, f, hst, hint, hfil⟩ := h
  let o : Submodule k W' ≃o Submodule k W := Submodule.orderIsoMapComap e.symm
  have ho : ∀ (U : Submodule k W') (v : W), v ∈ o U ↔ e v ∈ U := by
    intro U v
    change v ∈ U.map (e.symm : W' →ₗ[k] W) ↔ _
    rw [Submodule.mem_map_equiv]
    simp
  have ho' : ∀ (U : Submodule k W) (v : W), e v ∈ o.symm U ↔ v ∈ U := by
    intro U v
    rw [← ho, o.apply_symm_apply]
  have hstab : ∀ U, Stable s' U → Stable s (o U) := by
    intro U hU g v hv
    rw [ho] at hv ⊢
    rw [he]
    exact hU g _ hv
  refine ⟨?_, m, fun j => o (Ws j), e.trans f, fun j => hstab _ (hst j), ?_, ?_⟩
  · intro U hU
    have hU' : Stable s' (o.symm U) := by
      intro g w hw
      obtain ⟨v, rfl⟩ := e.surjective w
      rw [← he, ho']
      exact hU g v ((ho' U v).1 hw)
    obtain ⟨U', h1, h2⟩ := hss _ hU'
    refine ⟨o U', hstab _ h1, ?_⟩
    have := o.isCompl h2
    rwa [o.apply_symm_apply] at this
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
    refine ⟨iSupIndep.map_orderIso o hint.1, ?_⟩
    rw [← o.map_iSup, hint.2, o.map_top]
  · intro j g v hv
    rw [ho] at hv
    obtain ⟨w, hw, hw'⟩ := hfil j g _ hv
    refine ⟨e.symm w, ?_, ?_⟩
    · have : (⨆ j' ∈ Set.Iio j, o (Ws j')) = o (⨆ j' ∈ Set.Iio j, Ws j') := by
        simp only [o.map_iSup]
      change e.symm w ∈ (⨆ j' ∈ Set.Iio j, o (Ws j'))
      rw [this, ho]
      simpa using hw
    · simpa [he] using hw'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqKerThetaOfDistinguishedAinf
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem span_eq_ker_theta_of_distinguished : ∀ (l : ℕ) [Fact l.Prime] (x : Ainf l), Per.θ l x = 0 →
    IsUnit ((ainfDelta l).δ x) → Ideal.span {x} = RingHom.ker (Per.θ l) := by
  intro l hl x hx hu
  obtain ⟨ξ, h, -, h1⟩ := GlobalTheory.Prism.exists_generator l
  have h0 : Per.θ l ξ = 0 := by rw [← RingHom.mem_ker, h]; exact Ideal.mem_span_singleton_self ξ
  obtain ⟨c, hc⟩ : ξ ∣ x := by
    rw [← Ideal.mem_span_singleton, ← h]; exact hx
  have hφ := (ainfDelta l).φ_eq x
  have hφ' : (ainfDelta l).φ x = WittVector.frobenius x := rfl
  have hfx : WittVector.frobenius x = WittVector.frobenius ξ * WittVector.frobenius c := by
    rw [hc, map_mul]
  rw [hφ', hfx] at hφ
  have h3 := congrArg (Per.θ l) hφ
  rw [map_mul, h1, map_add, map_pow, map_mul, map_natCast, hx,
    zero_pow hl.out.ne_zero, zero_add] at h3
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h4 : v * WittVector.frobenius c - 1 ∈ Ideal.span {ξ} := by
    rw [← h, RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero]
    have h5 : Per.θ l (WittVector.frobenius c) = Per.θ l ((ainfDelta l).δ x) :=
      mul_left_cancel₀ (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : OC l) ≠ 0) h3
    rw [h5, ← map_mul, hv, map_one]
  have := (GlobalTheory.Per.AinfComplete.main l ξ fun hu =>  (hu.map (Per.θ l)).ne_zero h0).2
  have h5 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h4) 1
  rw [mul_one, sub_add_cancel] at h5
  have h6 : IsUnit c := by
    rw [← (WittVector.frobeniusEquiv l (OCb l)).symm_apply_apply c]
    exact (isUnit_of_mul_isUnit_right h5).map (WittVector.frobeniusEquiv l (OCb l)).symm
  rw [h, hc, Ideal.span_singleton_mul_right_unit h6]

end GlobalTheory.BSP
end
end

