import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0626
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0620
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryHeckeCharacterTrivialTamePart
section
noncomputable section

namespace GlobalTheory.LamTie.TeichEx

section General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.GridChars GlobalTheory.CMVal
open GlobalTheory.LamTie.AuxiliaryPrimeFunction

variable {L : Type} [Field L] [NumberField L]

theorem coprime_absNorm_sub_one (v : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime) (hv : (p : 𝓞 L) ∈ v.asIdeal) :
    Nat.Coprime p (Ideal.absNorm v.asIdeal - 1) := by
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI := v.isPrime
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 L ⧸ v.asIdeal) = 0 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← nsmul_one, card_nsmul_eq_zero']
  have h1 := GlobalTheory.Mem.WildChar.one_lt_absNorm v
  have hp0 : ((p : ℕ) : 𝓞 L ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem.2 hv]
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun ⟨t, ht⟩ => one_ne_zero (α := 𝓞 L ⧸ v.asIdeal) ?_
  have e : Ideal.absNorm v.asIdeal = p * t + 1 := by omega
  rw [e] at hN
  simpa [hp0] using hN

theorem exists_char_teich {F : Type} [Field F] [NumberField F] [Algebra F L] {c : L ≃ₐ[F] L} {I : Type} [Fintype I]
    {φ : I → L →+* ℂ} (hcm : CMData F c φ) (e : I → ℤ) (O : HeightOneSpectrum (𝓞 L) → Prop) (hfin : {w | O w}.Finite)
    (hO : ∀ w w', w.under (𝓞 F) = w'.under (𝓞 F) → O w → O w') (w0 : HeightOneSpectrum (𝓞 L)) (h0 : ¬ O w0)
    (hpr : ∀ w, O w → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal) {q : ℕ} (hq : q.Prime) (h5 : Units.torsionOrder L + 1 < q)
    (hq0 : (q : 𝓞 L) ∈ w0.asIdeal)
    (hsp : ∀ w, O w ∨ w.under (𝓞 F) = w0.under (𝓞 F) → ¬ ConjPl c.toRingEquiv w w) :
    ∃ χ : Formalism.L2.Host.HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => 2 * e i) ∧
      (∀ w, ¬ O w → w.under (𝓞 F) ≠ w0.under (𝓞 F) → χ.UnrAt w) ∧ (∀ w, O w → ExpAt χ w 2) ∧
      (∀ w, w.under (𝓞 F) = w0.under (𝓞 F) → ExpAt χ w 1) ∧
      ∀ w, O w → ∀ x : (w.adicCompletion L)ˣ, x ^ (Ideal.absNorm w.asIdeal - 1) = 1 → χ.loc w x = 1 := by
  classical
  haveI : Nonempty (HeightOneSpectrum (𝓞 L)) := ⟨w0⟩
  let u : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 F) := fun w => w.under (𝓞 F)
  let r : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 L) := fun w => Function.invFun u (u w)
  have hr : ∀ w, (r w).under (𝓞 F) = w.under (𝓞 F) := fun w => Function.invFun_eq (f := u) ⟨w, rfl⟩
  have hrr : ∀ w w', w.under (𝓞 F) = w'.under (𝓞 F) → r w = r w' := fun w w' h => congrArg (Function.invFun u) h
  set w1 := r w0 with hw1
  have hu1 : w1.under (𝓞 F) = w0.under (𝓞 F) := hr w0
  have h1 : ¬ O w1 := fun h => h0 (hO _ _ hu1 h)
  let S : Finset (HeightOneSpectrum (𝓞 L)) := insert w1 (hfin.toFinset.filter fun w => r w = w)
  have hS : ∀ w, w ∈ S ↔ w = w1 ∨ (O w ∧ r w = w) := fun w => by simp [S]
  have hfix : ∀ w ∈ S, r w = w := fun w hw => by
    rcases (hS w).1 hw with rfl | h
    exacts [hrr _ _ hu1, h.2]
  have hne : ∀ w, O w → w ≠ w1 := fun w hw h => h1 (h ▸ hw)
  have hwild : ∀ w : HeightOneSpectrum (𝓞 L), ∃ θ : (w.adicCompletion L)ˣ →* ℂˣ,
      O w → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal ∧ (∀ x, θ x ^ p = 1) ∧
        (∀ x, IsUnitAt w x → Valued.v ((x : w.adicCompletion L) - 1) ≤ WithZero.exp (-2 : ℤ) → θ x = 1) ∧
        ∃ k : Lˣ, IsUnitAt w (atFin w k) ∧
          Valued.v (((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1) ≤
            WithZero.exp (-1 : ℤ) ∧ θ (atFin w k) ≠ 1 := fun w => by
    by_cases hw : O w
    · obtain ⟨p, hp, hp'⟩ := hpr w hw
      obtain ⟨θ, hθ⟩ := exists_wild w hp hp'
      exact ⟨θ, fun _ => ⟨p, hp, hp', hθ⟩⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose θ1 hθ1 using hwild
  have hw0 : w1 ∈ S := (hS _).2 (Or.inl rfl)
  obtain ⟨θ0, ht0, hθ0, k0, hk0, hk0'⟩ := exists_tame_par w1 hq h5 (natCast_mem_of_under hu1.symm hq0) φ e (S.erase w1) θ1
  let θ : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ →* ℂˣ := Function.update θ1 w1 θ0
  have e0 : θ w1 = θ0 := Function.update_self _ _ _
  have e1 : ∀ w, w ≠ w1 → θ w = θ1 w := fun w hw => Function.update_of_ne hw _ _
  obtain ⟨χ, hu, ht, hi, hunr, hloc⟩ := exists_hecke_level hcm e S θ
    (fun w hw => by
      rcases (hS w).1 hw with rfl | ⟨h2, -⟩
      · rw [e0]; exact GlobalTheory.ModelChar.continuous_of_tameLoc ht0
      · obtain ⟨p, -, -, -, h, -⟩ := hθ1 w h2
        rw [e1 w (hne w h2)]; exact continuous_of_level h)
    (fun w hw x => by
      rcases (hS w).1 hw with rfl | ⟨h2, -⟩
      · rw [e0]; exact ht0.1 x
      · obtain ⟨p, hp, -, h, -⟩ := hθ1 w h2
        rw [e1 w (hne w h2)]
        exact Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]) hp.ne_zero)
    (fun w hw w' hcj hw' => by
      have := (under_eq_iff_conjPl c hcm.rank hcm.ne _ _).2 (Or.inr hcj)
      obtain rfl : w' = w := by rw [← hfix w' hw', hrr _ _ this, hfix w hw]
      refine hsp w' ?_ hcj
      rcases (hS w').1 hw with rfl | h
      exacts [Or.inr hu1, Or.inl h.1])
    (fun k hk => by
      have ep : ∏ w ∈ S.erase w1, θ w (atFin w k) = ∏ w ∈ S.erase w1, θ1 w (atFin w k) :=
        Finset.prod_congr rfl fun w hw => by rw [e1 w (Finset.ne_of_mem_erase hw)]
      rw [← Finset.mul_prod_erase _ _ hw0, e0, ep]
      exact hθ0 k hk)
  refine ⟨χ, hu, ht, hi, fun Q hQ hQ' => hunr Q fun w hw h => ?_, fun Q hQ => ?_, fun Q hQ => ?_, fun Q hQ x hx => ?_⟩
  · rcases (hS w).1 hw with rfl | h2
    exacts [hQ' (h.trans hu1), hQ (hO _ _ h.symm h2.1)]
  · have hOr : O (r Q) := hO _ _ (hr Q).symm hQ
    obtain ⟨σ, s1, s2, s3, -, s5⟩ := hloc (r Q) ((hS _).2 (Or.inr ⟨hOr, hrr _ _ (hr Q)⟩)) Q (hr Q).symm
    obtain ⟨p, -, -, -, t2, k, t3, t4, t5⟩ := hθ1 _ hOr
    rw [e1 _ (hne _ hOr)] at s5
    refine expAt_succ (n := 1) (fun x hx hx' => (s5 x hx).2 (t2 _ ((s2 x).2 hx) (by rw [s3]; exact hx'))) fun H => t5 ?_
    obtain ⟨x, hx⟩ := s1 k
    rw [← hx] at t3 t4 ⊢
    rw [s3] at t4
    exact (s5 x ((s2 x).1 t3)).1 (H x ((s2 x).1 t3) t4)
  · obtain ⟨σ, s1, s2, s3, -, s5⟩ := hloc w1 hw0 Q (hQ.trans hu1.symm)
    rw [e0] at s5
    refine expAt_succ (n := 0) (fun x hx hx' => (s5 x hx).2 (ht0.2 _ ((s2 x).2 hx) (by rw [s3]; exact hx'))) fun H => hk0' ?_
    obtain ⟨x, hx⟩ := s1 k0
    rw [← hx] at hk0 ⊢
    exact (s5 x ((s2 x).1 hk0)).1 ((χ.unrAt_iff Q).2 H x ((s2 x).1 hk0))
  · have hOr : O (r Q) := hO _ _ (hr Q).symm hQ
    obtain ⟨σ, -, -, -, s4, s5⟩ := hloc (r Q) ((hS _).2 (Or.inr ⟨hOr, hrr _ _ (hr Q)⟩)) Q (hr Q).symm
    obtain ⟨p, hp, hpm, t1, -⟩ := hθ1 _ hOr
    rw [e1 _ (hne _ hOr)] at s5
    have hpQ : (p : 𝓞 L) ∈ Q.asIdeal := natCast_mem_of_under (hr Q) hpm
    refine (s5 x (GlobalTheory.LamTie.isUnitAt_of_pow_eq_one hx)).2 ?_
    have a2 : θ1 (r Q) (σ x) ^ (Ideal.absNorm Q.asIdeal - 1) = 1 := by rw [← map_pow, s4 x _ hx, map_one]
    have : θ1 (r Q) (σ x) ^ Nat.gcd p (Ideal.absNorm Q.asIdeal - 1) = 1 := by
      rw [pow_gcd_eq_one]; exact ⟨t1 _, a2⟩
    rwa [Nat.Coprime.gcd_eq_one (coprime_absNorm_sub_one Q hp hpQ), pow_one] at this

end General

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
open GlobalTheory.LamTie.AuxiliaryPrimeFunction

theorem exists_auxiliaryHeckeCharacter_trivial_tame_part : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)) (c : R.Psi → ℤ),
    PlacesOk H q0 w0 → Units.torsionOrder H.E + 1 < q0 → ∃ χ, IsAuxiliaryHeckeCharacter H w0 c χ ∧ TeichTriv H χ := by
  intro R H q0 w0 c hP h5
  obtain ⟨cc, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  haveI : IsCMField H.E := H.isCMField_hostE
  have hd := hP.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil] at hd
  have hq := hP.splits q0 (by simp)
  have hpr : ∀ w, Over4 H w → ∃ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p ≠ q0 ∧ (p : 𝓞 H.E) ∈ w.asIdeal := by
    rintro w (⟨k, h⟩ | h | h)
    · fin_cases k
      · exact ⟨H.g 0, by simp, by tauto, h⟩
      · exact ⟨H.g 1, by simp, by tauto, h⟩
    · exact ⟨H.pde, by simp, by tauto, h⟩
    · exact ⟨H.pde', by simp, by tauto, h⟩
  have hsp : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ w : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ w.asIdeal →
      ¬ GlobalTheory.Mem.Chr.ConjPl cc.toRingEquiv w w := fun p hp w hw hc => by
    obtain ⟨h1, -, h2, h3⟩ := hP.splits p hp
    obtain ⟨P, P', hne, hP1, hP2⟩ := GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm H.E p h1 h2 h3 w hw
    have key : ∀ Q, GlobalTheory.CMVal.Over Q (below w) → Q = w := fun Q hQ => by
      rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl cc hcm.rank hcm.ne w Q).1 (HeightOneSpectrum.ext hQ) with h | h
      · exact h
      · exact (GlobalTheory.Mem.Chr.existsUnique_conjPl cc.toRingEquiv w).unique h hc
    exact hne ((key P hP1).trans (key P' hP2).symm)
  obtain ⟨χ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_char_teich hcm c (Over4 H)
    ((((finite_over (L := H.E) (hP.splits (H.g 0) (by simp)).1).union (finite_over (hP.splits (H.g 1) (by simp)).1)).union
      ((finite_over (hP.splits H.pde (by simp)).1).union (finite_over (hP.splits H.pde' (by simp)).1))).subset (by
        rintro w (⟨k, h⟩ | h | h)
        · fin_cases k
          exacts [Or.inl (Or.inl h), Or.inl (Or.inr h)]
        exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]))
    (by
      rintro w w' h (⟨k, h'⟩ | h' | h')
      exacts [Or.inl ⟨k, natCast_mem_of_under h h'⟩, Or.inr (Or.inl (natCast_mem_of_under h h')),
        Or.inr (Or.inr (natCast_mem_of_under h h'))])
    w0 (fun h => by
      obtain ⟨p, hp, h1, h2⟩ := hpr w0 h
      exact h1 (prime_eq (hP.splits p hp).1 hq.1 h2 hP.referencePlaceOverPrime))
    (fun w h => by
      obtain ⟨p, hp, -, h2⟩ := hpr w h
      exact ⟨p, (hP.splits p hp).1, h2⟩)
    hq.1 h5 hP.referencePlaceOverPrime
    (by
      rintro w (h | h)
      · obtain ⟨p, hp, -, h2⟩ := hpr w h
        exact hsp p hp w h2
      · exact hsp q0 (by simp) w (natCast_mem_of_under h.symm hP.referencePlaceOverPrime))
  exact ⟨χ, ⟨h1, h2, ⟨fun g => 2 * c g, fun g => by push_cast; rfl, h3⟩, h4, h5, h6⟩, fun w hw => h7 w (Or.inr hw)⟩

end GlobalTheory.LamTie.TeichEx

namespace GlobalTheory.LamTie

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

end GlobalTheory.LamTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedSemistablePeriodsNullFamily
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem exists_bounded_periods_wseed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∃ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (k : ℕ) (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (Z : ι → Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (∀ (n : ℕ) (a b : Fin d), {i | v i a b ∉ (bk.J ^ n).map bk.ev}.Finite) ∧ (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ i, s.W * (Z i).map j = (v i).map bk.iA) ∧ ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * TB.b i)) (bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0)) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hρ0 := bk.ρ₀_pos'
  have hρ1 := bk.ρ₀_lt_one'
  have hj0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ :=
    Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj0
  have hj0d : IsDiscMap bk.ev j0 := isDiscMap_map _ _
  have hΦ0 : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀ := by
    rw [frobenius_ev_X_eq]
    refine (norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ0).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero
  let Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ :=
    Disc.map (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) WittVector.frobenius hΦ0
  have hΦ : IsDiscMap WittVector.frobenius Φ := isDiscMap_map _ _
  obtain ⟨cD, hc1, hc2, hc3, hc4, hc5, -, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0d
  have hrec := GlobalTheory.T.semistable_disc_coefficient_recurrence l K bk τ hτ d ρ hρ s ι TB j0 hj0d cD hc1 hc2 hc5 hc3 Φ hΦ
  let V : ι → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := fun i => s.W * (s.W'.map (cD i)).map j0
  let Vκ : ι × (Fin d × Fin d) → bk.DA bk.ρ₀ := fun p => V p.1 p.2.1 p.2.2
  let c : ι × (Fin d × Fin d) → ι × (Fin d × Fin d) → Ainf l := fun p q =>
    if p.2 = q.2 then bk.ev (TB.c q.1 (WittVector.frobenius (TB.b p.1))) else 0
  have hcfin : ∀ p (n : ℕ), {q | c p q ∉ (bk.J ^ n).map bk.ev}.Finite := by
    rintro ⟨i, ab⟩ n
    refine ((TB.fin (WittVector.frobenius (TB.b i)) n).image fun i₁ => (i₁, ab)).subset ?_
    rintro ⟨i₁, ab'⟩ hq
    by_cases e : ab = ab'
    · subst e
      refine ⟨i₁, fun hm => hq ?_, rfl⟩
      simp only [c, if_pos rfl]
      exact Ideal.mem_map_of_mem _ hm
    · exact (hq (by simp [c, e])).elim
  have hj0c : Continuous j0 :=
    AddMonoidHomClass.continuous_of_bound j0 1 fun y => (hj0d.norm_le y).trans (one_mul _).ge
  have hV : Filter.Tendsto Vκ Filter.cofinite (nhds 0) := by
    refine tendsto_cofinite_prod_of_finite Vκ fun ab => ?_
    have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun m _ =>
      (tendsto_const_nhds (x := s.W ab.1 m)).mul ((hj0c.tendsto 0).comp (hc4 (s.W' m ab.2)))
    simpa [Vκ, V, Matrix.mul_apply] using this
  have hrecκ : ∀ q, HasSum (fun p => Φ (Vκ p) * toDisc l (bk.ev X) bk.ρ₀ (c p q))
      (toDisc l (bk.ev X) bk.ρ₀ (bk.ev bk.E) ^ (2 * s.N) * Vκ q) := by
    rintro ⟨i₁, a, b⟩
    have hg : Function.Injective (fun i : ι => (i, (a, b))) := fun x y h => (Prod.mk.inj h).1
    refine (hg.hasSum_iff ?_).1 ?_
    · rintro ⟨i, a', b'⟩ hx
      have hne : (a', b') ≠ (a, b) := fun e => hx ⟨i, by simp [e]⟩
      simp [c, hne]
    · convert hrec i₁ a b using 1
      · funext i
        simp [c, Vκ, V]
      · rfl
  obtain ⟨k, v, hv1, hv2⟩ := GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk (Ainf l) bk.ev ι TB WittVector.frobenius (frobenius_ev_X_eq bk)
    Φ hΦ _ c hcfin (2 * s.N) Vκ hV hrecκ
  refine ⟨ι, TB, k, fun i => Matrix.of fun a b => v (i, (a, b)),
    fun i => (l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i), ?_, ?_, ?_⟩
  · intro n a b
    have hg : Function.Injective (fun i : ι => (i, (a, b))) := fun x y h => (Prod.mk.inj h).1
    exact (hv2 n).preimage hg.injOn
  · intro j hj i
    have e := IsDiscMap.unique hj hj0d
    subst e
    ext a b
    show (s.W * ((l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i)).map j0) a b = bk.iA (v (i, (a, b)))
    rw [hv1]
    simp only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow,
      map_natCast, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  · intro a b
    have hs := (hasSum_sum (s := (Finset.univ : Finset (Fin d))) fun m _ =>
      (hc5 (s.W' m b)).mul_left (s.W a m)).mul_left ((l : bk.DA bk.ρ₀) ^ k)
    have hW := congrFun (congrFun s.W_mul a) b
    rw [Matrix.mul_apply] at hW
    rw [hW] at hs
    have hf : (fun i => bk.iA ((Matrix.of fun a b => v (i, (a, b))) a b * TB.b i)) =
        fun i => (l : bk.DA bk.ρ₀) ^ k * ∑ m, s.W a m * (j0 (cD i (s.W' m b)) * toDisc l (bk.ev X) bk.ρ₀ (TB.b i)) := by
      funext i
      rw [map_mul, Matrix.of_apply, hv1]
      simp only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hval : bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0) =
        (l : bk.DA bk.ρ₀) ^ k * (bk.iA τ ^ (2 * s.N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) a b := by
      rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [hf, hval]
    exact hs

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
section
noncomputable section

namespace GlobalTheory.SmGL.DepthZero

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.StepData ValuativeRel
open scoped TensorProduct

section Tensor

variable {α : Type} [Fintype α] [dec : DecidableEq α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def contract (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) : (⨂[ℂ] b, X b) →ₗ[ℂ] X a := GlobalTheory.MultilinearContraction.contract φ a

theorem contract_tprod (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (x : ∀ b, X b) :
    contract φ a (PiTensorProduct.tprod ℂ x) = (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a :=
  GlobalTheory.MultilinearContraction.contract_tprod φ a x

theorem exists_contract_ne_zero {w : ⨂[ℂ] b, X b} (hw : w ≠ 0) (a : α) :
    ∃ φ : ∀ a, X a →ₗ[ℂ] ℂ, contract φ a w ≠ 0 := by
  let b := fun i => Module.Free.chooseBasis ℂ (X i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr w p ≠ 0 := by
    by_contra! h
    exact hw (B.repr.injective (by ext p; simp [h p]))
  refine ⟨fun i => (b i).coord (p i), fun h => hp ?_⟩
  have key : (b a).coord (p a) ∘ₗ contract (fun i => (b i).coord (p i)) a = B.coord p := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contract_tprod, map_smul,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  have := congrArg (fun L => L w) key
  simp only [LinearMap.comp_apply, h, map_zero, Module.Basis.coord_apply] at this
  exact this.symm

theorem contract_piTensor {Γ : α → Type} [∀ a, Group (Γ a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (g : Γ a) (w : ⨂[ℂ] b, X b) :
    contract φ a (piTensor ρ (Pi.mulSingle a g) w) = ρ a g (contract φ a w) := by
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_tprod c x =>
    simp only [map_smul, piTensor_tprod, contract_tprod, Pi.mulSingle_eq_same]
    congr 2
    exact Finset.prod_congr rfl fun b hb => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb)]; simp

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_KOne₁ : IsCompact (KOne k n : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_KOne) KOne_le_KO

theorem conj_mem_KOne₁ {w g : GL n k} (hw : w ∈ KO k n) (hg : g ∈ KOne k n) : w⁻¹ * g * w ∈ KOne k n := by
  refine mem_KOne.2 ?_
  have : (w⁻¹ * g * w).val - 1 = (w⁻¹).val * (g.val - 1) * w.val := by
    simp [mul_sub, sub_mul]
  rw [this]
  exact ((mem_KO.1 hw).2.mul_maxM (mem_KOne.1 hg)).mul_intM (mem_KO.1 hw).1

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem leviEmb_mem_KOne₁ (e : (Σ a, m a) ≃ n) {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) :
    leviEmb k e g ∈ KOne k n := by
  refine mem_KOne.2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := mem_KOne.1 (hg a) i j
    simpa [Matrix.sub_apply, Matrix.one_apply] using this
  · have h' : e ⟨a, i⟩ ≠ e ⟨b, j⟩ := fun h' => h (congrArg Sigma.fst (e.injective h'))
    simp [Matrix.sub_apply, leviEmb_apply_ne k e g h, Matrix.one_apply_ne h']

theorem deltaHalf_eq_one {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => tame_det_of_mem_KOne (fun x hx => isUnram_absPow k _ x ?_) (hg a)
  simpa using Valuation.map_one_add_of_lt _ hx

theorem exists_fixed_of_parInd (e : (Σ a, m a) ≃ n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k m) W) {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) (KOne k n)) (h0 : f ≠ 0) :
    ∃ w : W, w ≠ 0 ∧ ∀ g : Levi k m, (∀ a, g a ∈ KOne k (m a)) → ρ g w = w := by
  obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
    by_contra! h
    exact h0 (Subtype.ext (Subtype.ext (funext h)))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  refine ⟨f.1.1 c, fun h => hx (by rw [parInd_law, h]; simp), fun g hg => ?_⟩
  have h1 := parInd_law e ρ f ⟨_, leviEmb_mem_parab k e g⟩ c
  rw [leviProj_leviEmb, deltaHalf_eq_one hg, Units.val_one, one_smul] at h1
  have h2 := hf ⟨_, conj_mem_KOne₁ hc (leviEmb_mem_KOne₁ e hg)⟩
  have h3 := congrArg (fun F : IndSp e ρ => F.1.1 c) h2
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul] at h3
  rw [← h1, ← h3]
  group

theorem fixed_of_isSubquotient (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL n k) V} (h : IsSubquotient π (multiProd e σ))
    (hv : ∃ v ∈ fixed π (KOne k n), v ≠ 0) (a : α) : ∃ v ∈ fixed (σ a) (KOne k (m a)), v ≠ 0 := by
  obtain ⟨S, F, hF⟩ := h
  obtain ⟨v, hv, hv0⟩ := hv
  obtain ⟨u, rfl⟩ := hF v
  have hS : IsSmooth S.toRepresentation := fun y => by
    have := isSmooth_parInd e (piTensor σ) y.1
    convert this using 3 with g
    exact Subtype.ext_iff
  obtain ⟨y, hy, hyu⟩ := IwahoriOnto.exists_fixed_map_eq hS isCompact_KOne₁ F.toLinearMap u fun g hg => by
    have h1 := hv ⟨g, hg⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact (F.isIntertwining _ _ g u).trans h1
  have hy0 : y.1 ≠ 0 := fun h => hv0 (by
    have : y = 0 := Subtype.ext h
    rw [this, map_zero] at hyu
    exact hyu.symm)
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_parInd e (piTensor σ) (f := y.1)
    (fun g => congrArg Subtype.val (hy g)) hy0
  obtain ⟨φ, hφ⟩ := exists_contract_ne_zero hw0 a
  refine ⟨_, fun g => ?_, hφ⟩
  rw [← contract_piTensor, hw _ fun b => ?_]
  · simp
  · by_cases hb : b = a
    · subst hb; simp
    · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

end GlobalTheory.SmGL.DepthZero

namespace GlobalTheory.SmGL

open GlobalTheory.PRep GlobalTheory.SplitRead

theorem depthZeroSupport : GlobalTheory.Published.DepthZeroSupport := by
  intro k _ _ _ _ n π s d σ h hv a
  obtain ⟨-, -, e, he⟩ := h
  exact DepthZero.fixed_of_isSubquotient e (fun a => (σ a).π) he hv a

end GlobalTheory.SmGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCrystalStratificationMatrixStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_crystal_stratification_matrix : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  first | exact @GlobalTheory.CrysStrat.exists_stratification | exact GlobalTheory.CrysStrat.exists_stratification | (intros; apply GlobalTheory.CrysStrat.exists_stratification <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantVectorExactFiltrationDegreeBcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (x : P.R.B), IsUnit x → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ₀' τ' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) (j : ℕ), (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀' ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1) → (∀ a : ↥(K0 K), τ' ((⇑(P.PD K).σ)^[j] a) = τ₀' a) → ∀ d : ℤ, P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil d → P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil (d + 1) → ∃ w ∈ DcrisL (P.PD K) (charRep μ) τ', ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) d ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1) := by
  first | exact @GlobalTheory.exists_letter_vector_exact_degree | exact GlobalTheory.exists_letter_vector_exact_degree | (intros; apply GlobalTheory.exists_letter_vector_exact_degree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRealizationMatrixStratifiedPhiModuleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realization_matrix_stratifiedPhiModule : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ S : Strat bk d, S.a = ht.a + s.N → S.A = ht.A → (∀ g : ↥(GK K), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA)) → ∃ T : Matrix (Fin d) (Fin d) (WCb l), MReal S ρ T := by
  first | exact @GlobalTheory.BSP.RealMatrix.exists_mreal | exact GlobalTheory.BSP.RealMatrix.exists_mreal | (intros; apply GlobalTheory.BSP.RealMatrix.exists_mreal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrimeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.hypL i := by
  first | exact @GlobalTheory.SplitDecl.main | exact GlobalTheory.SplitDecl.main | (intros; apply GlobalTheory.SplitDecl.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionsLowAndPullbackRecord
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LowLevel

set_option maxHeartbeats 1000000 in

theorem expansions_low_and_pullback_record : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ (i : Let K) (ζ : ↥LL.1), (∃ m : ℕ, ζ ^ (((D.loc l).PD K).p ^ m) = 1) → PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 → (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : AA K LL) • x) k ∈ ιDi W T i ∧ (k < 0 → W.levN T i ζ x k = 0)) ∧ Submodule.span ↥LL.1 (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : AA K LL) • x) 0) = ιDi W T i) ∧ ∀ (i : Let K) (ζ : ↥LL.1) τ, ptK D.loc HW h i ζ τ → (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), W.levN T i ζ ⟨_, hk⟩ j ∈ ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧ Submodule.span ↥LL.1 {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T), w = W.levN T i ζ ⟨_, hk⟩ k} = ιDi W T i :=
  expansions_low_and_pullback

end GlobalTheory.NL.LowLevel
end

