import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0671
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
import Formalism.AdmissibleDesigns.Bundle0001
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HeckeDetChar

open Formalism.L2.JoinChr
open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem place_eq {e : AE D} {P P' : Pl D.host.E} (h : IsIdemAt e P) (h' : IsIdemAt e P') : P = P' := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [h.2 x hx, h'.2 x hx]

theorem finPart_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : finPart D e ∈ intAE D := by
  by_contra hc
  have := (he.2 1 one_ne_zero).2 (by
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem finPart_mul_incA_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) {x : D.host.E}
    (hx : P.valuation D.host.E x ≤ 1) : finPart D (e * incA D x) ∈ intAE D := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx
  have hd : (d : 𝓞 D.host.E) ∉ P.asIdeal := d.2
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  have hdE : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h0; apply hd0; exact RingOfIntegers.ext h0
  have hxe : x = (n : D.host.E) * ((d : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hdE]; exact h
  have h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D :=
    not_not.1 (mt (he.2 _ hd0).2 hd)
  rw [hxe, RingHom.map_mul (incA D), show e * (incA D (n : D.host.E) * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) =
    incA D (n : D.host.E) * (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) by ring, RingHom.map_mul (finPart D)]
  exact GlobalTheory.HeckeConj.mul_mem_intAE D (GlobalTheory.SplitIndex.finPart_incA_mem n) h1

theorem idem_mul_eq_zero {Q : Finset (Pl D.host.E)} (hS : SplitSet Q) {P : Pl D.host.E}
    (hoff : Bridge.SplitOff P (Q : Set (Pl D.host.E))) {e : AE D} (he : IsIdemAt e P) :
    (idem Q + cA D (idem Q)) * e = 0 := by
  have hc : IsIdemAt (cA D e) (conjPl P) := GlobalTheory.MovedIdem.isIdemAt_conj he fun _ => Iff.rfl
  rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_eq_zero fun Q' hQ' => ?_
  have he' := hS.isIdemAt hQ'
  rw [add_mul]
  have a1 : idemAt Q' * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 he.1 with h | h
    · rw [h] at he'
      exact absurd (place_eq he he' ▸ hQ' : P ∈ (Q : Set (Pl D.host.E))) hoff.2.1
    · exact h
  have a2 : cA D (idemAt Q') * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 hc.1 with h | h
    · rw [h] at he'
      have hPQ := place_eq hc he'
      refine absurd ?_ (hoff.2.2 Q' hQ')
      rw [← hPQ]
      ext x
      rw [Formalism.L2.Col.mem_conjIdeal]
      rfl
    · have := congrArg (cA D) h
      rwa [map_mul, GlobalTheory.MovedIdem.cA_cA, map_zero] at this
  rw [a1, a2, add_zero]

theorem chi_eq_one {χ : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)} (hχ : GlobalTheory.ExportSeries.UnramOutside χ Q)
    {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) (hQ : (idem Q + cA D (idem Q)) * e = 0) (x : (AE D)ˣ)
    (y y' : AE D) (hx : (x : AE D) = 1 + e * (y - 1)) (hx' : ((x⁻¹ : (AE D)ˣ) : AE D) = 1 + e * (y' - 1))
    (hy : finPart D (e * y) ∈ intAE D) (hy' : finPart D (e * y') ∈ intAE D) : χ x = 1 := by
  have key : ∀ w : AE D, finPart D (e * w) ∈ intAE D → finPart D (1 + e * (w - 1)) ∈ intAE D := fun w hw => by
    rw [show 1 + e * (w - 1) = 1 - e + e * w by ring, RingHom.map_add, RingHom.map_sub, RingHom.map_one]
    exact add_mem (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) (finPart_mem he)) hw
  refine hχ x ?_ ?_ ?_ ?_
  · rw [hx, RingHom.map_add, RingHom.map_one, RingHom.map_mul, GlobalTheory.StepVec.infPart_idemAt he, zero_mul, add_zero]
  · rw [hx]; exact key y hy
  · rw [hx']; exact key y' hy'
  · rw [hx, mul_add, mul_one, ← mul_assoc, hQ, zero_mul, add_zero]

theorem locE_pow {e : AE D} (he : e * e = e) (a : AE D) (k : ℕ) :
    (1 + e * (a - 1)) ^ k = 1 + e * (a ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    linear_combination (a ^ k - 1) * (a - 1) * he

theorem isPlIdem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : IsPlIdem D e P := by
  obtain ⟨⟨h1, h2, v, ε, hv, hs⟩, h3⟩ := he
  exact ⟨h1, ⟨v, ε, hv, Or.inl ⟨h2, hs⟩⟩, h3⟩

theorem locU_inv {e : AE D} (he : e * e = e) (k : D.host.Eˣ) :
    (((locU he k)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
  have hmul : locU he k * locU he k⁻¹ = 1 := by
    apply Units.ext
    rw [Units.val_mul, locU_val, locU_val, locE_mul_locE he, Units.mul_inv, Units.val_one]
    simp [locE]
  rw [inv_eq_of_mul_eq_one_right hmul, locU_val]

theorem val_unif {P : Pl D.host.E} {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) :
    P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact hP2 (zero_mem _)
  rw [show (ϖ : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ϖ from rfl, P.valuation_of_algebraMap]
  have a1 := (P.intValuation_lt_one_iff_mem ϖ).2 hP
  have a2 := (P.intValuation_le_pow_iff_mem ϖ 2).not.2 hP2
  rw [P.intValuation_eq_exp_neg_multiplicity hϖ0] at a1 a2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at a1
  rw [WithZero.exp_le_exp] at a2
  congr 1
  push_cast at a2
  omega

theorem chi_detAt : ∀ {D : D7} {χ : (AE D)ˣ →* Circle} {c : Formalism.L2.Host.HChar D.host.E}, ChrEq χ c →
    ∀ {Q : Finset (Pl D.host.E)}, GlobalTheory.ExportSeries.UnramOutside χ Q → GlobalTheory.ExportSeries.SplitSet Q → ∀ {P : Pl D.host.E},
    Bridge.SplitOff P (Q : Set (Pl D.host.E)) → ∀ {V : HSp D} {k : ℕ} {α : GA D V}, IsHeckeAt V P k α →
    ∀ {z : (AE D)ˣ}, IsDetAt (idemAt P) V α z → ((χ z : Circle) : ℂ) = ((c.val P : ℂˣ) : ℂ) ^ k := by
  intro D χ c hχc Q hU hS P hoff V k α hα z hz
  obtain ⟨e, ϖ, he, hϖP, hϖP2, hH⟩ := hα
  rw [idemAt_eq he] at hz
  obtain ⟨-, -, -, -, u, u', hu, hu', huu, hdet⟩ := hH
  have hQe := idem_mul_eq_zero hS hoff he
  have hee : e * e = e := he.1.1
  have hv := val_unif hϖP hϖP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  set ϖU : D.host.Eˣ := Units.mk0 (ϖ : D.host.E) hϖ0 with hϖU

  let wU : (AE D)ˣ := ⟨1 + e * (u - 1), 1 + e * (u' - 1),
    by linear_combination (u - 1) * (u' - 1) * hee + huu,
    by linear_combination (u - 1) * (u' - 1) * hee + huu⟩
  have hw : χ wU = 1 := chi_eq_one hU he hQe wU u u' rfl rfl
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu)
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu')

  have hz' : z = locU hee ϖU ^ k * wU := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, locU_val, locE, locE_pow hee, hz]
    show e * (mt V α).det + (1 - e) = (1 + e * (incA D (ϖ : D.host.E) ^ k - 1)) * (1 + e * (u - 1))
    linear_combination hdet - (incA D (ϖ : D.host.E) ^ k - 1) * (u - 1) * hee

  have h1 : ((χ (locU hee ϖU) : Circle) : ℂ) = ((c.locK P ϖU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) ϖU _ (locU_val hee ϖU)

  set rU : D.host.Eˣ := ϖU * (Formalism.L2.Host.unif P)⁻¹ with hrU
  have hvπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) := by
    have := Formalism.L2.Host.unif_spec P
    unfold Formalism.L2.Host.IsUnifAt at this
    rw [← this]
    show _ = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) _)
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm
  have hvr : P.valuation D.host.E (rU : D.host.E) = 1 := by
    rw [hrU, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπ, hϖU, Units.val_mk0, hv]
    exact mul_inv_cancel₀ (WithZero.exp_ne_zero)
  have hr1 : χ (locU hee rU) = 1 := by
    refine chi_eq_one hU he hQe _ (incA D (rU : D.host.E)) (incA D ((rU⁻¹ : D.host.Eˣ) : D.host.E)) rfl
      (locU_inv hee rU) (finPart_mul_incA_mem he hvr.le) (finPart_mul_incA_mem he ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvr, inv_one]
  have hr2 : ((χ (locU hee rU) : Circle) : ℂ) = ((c.locK P rU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) rU _ (locU_val hee rU)
  rw [hr1] at hr2
  have hval : ((c.locK P ϖU : ℂˣ) : ℂ) = ((c.val P : ℂˣ) : ℂ) := by
    have : ϖU = rU * Formalism.L2.Host.unif P := by rw [hrU, inv_mul_cancel_right]
    rw [this, map_mul, Units.val_mul, ← hr2, Formalism.L2.Host.HChar.val]
    simp
  rw [hz', map_mul, map_pow, hw, mul_one, Circle.coe_pow, h1, hval]

end GlobalTheory.HeckeDetChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfMemSupport
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AVGood

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_of_toral {x : IrrGL k} (h : Toral x) : Good x := by
  obtain ⟨s, hs, h1⟩ := h
  exact ⟨s, hs, fun y hy => Or.inl (h1 y hy)⟩

theorem fixed_ne_bot_of_mem_support {x : IrrGL k} (hx : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥)
    {s : Multiset (IrrGL k)} (hs : HasSupport x.rep s) {y : IrrGL k} (hy : y ∈ s) :
    fixed y.rep (KOne k (Fin y.1)) ≠ ⊥ := by
  obtain ⟨h, z, rfl, -, -, e, he⟩ := hs
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hx
  obtain ⟨w, hw, hw0⟩ := DepthZero.fixed_of_isSubquotient e (fun a => (z a).rep) he ⟨v, hv, hv0⟩ a
  exact (Submodule.ne_bot_iff _).2 ⟨w, hw, hw0⟩

theorem good_of_fixed_KOne (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hk : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i) (x : IrrGL k)
    (hx : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥) : Good x := by
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ x
  exact ⟨s, hs, fun y hy => Or.inr ⟨hk, y, 1, isSmoothChar_one, fixed_ne_bot_of_mem_support hx hs hy,
    (IrrGL.tw_one y _).symm⟩⟩

theorem good_of_isSpherical (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (x : IrrGL k) (hx : IsSpherical x.rep) :
    Good x :=
  (GlobalTheory.SphSupport.toral_and_good_of_isSpherical hBZ k x hx).2

end Local

def TameAtG (D : D7) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ (i : D.nd.Loc) (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E)
    (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.w = D.naut.plGw k v →
    NG.IsCompAt (tup (D.nd.mu i) j) s ξ → ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1

end GlobalTheory.AVGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentAddConjSupportFinitePrimeToPStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q)) → ∀ (p : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite ∧ (∀ Q ∈ S, (p : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ∀ Q ∉ S, ι (finPart D (e + cA D e)) Q = 0 := by
  first | exact @GlobalTheory.idemSum_add_conj_support_finite | exact GlobalTheory.idemSum_add_conj_support_finite | (intros; apply GlobalTheory.idemSum_add_conj_support_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFiniteStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → (∀ Q ∈ S, (p : 𝓞 E) ∉ Q.asIdeal) → (∀ Q ∉ S, ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p G.1 ∧ Bnd p (G⁻¹).1 := by
  first | exact @GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | exact GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | (intros; apply GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCuspidal_of_isSubquotient {n V W : Type} [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W}
    (hτ : IsCuspidal τ) (h : IsSubquotient π τ) : IsCuspidal π := by
  refine ⟨h.isSmooth hτ.1, fun s d e he => ?_⟩
  obtain ⟨S, f, hf⟩ := GlobalTheory.JacquetExact.isSubquotient_jac e hτ.1 h
  haveI := hτ.2 s d e he
  exact hf.subsingleton

theorem exists_root_norm {ω : kˣ →* ℂˣ} (hω : IsSmoothChar ω) {b : ℕ} (hb : 0 < b) :
    ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ ∀ z, ‖((ω * ψ ^ b) z : ℂ)‖ = 1 := by
  let f : kˣ →* ℂ :=
    { toFun := fun z => ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ)
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, Units.val_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul] }
  refine ⟨f.toHomUnits, Subgroup.isOpen_mono (H₁ := ω.ker) (fun z hz => ?_) hω, fun z => ?_⟩
  · refine Units.ext ?_
    have hz' : ω z = 1 := hz
    show ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ) = 1
    rw [hz']; simp
  · have h0 : 0 < ‖(ω z : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have e : ((f.toHomUnits z : ℂˣ) : ℂ) = ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ) := rfl
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, e, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h0.le _), ← Real.rpow_natCast, ← Real.rpow_mul h0.le,
      neg_mul, inv_mul_cancel₀ (by positivity), Real.rpow_neg_one, mul_inv_cancel₀ h0.ne']

theorem exists_irreducible_sub {b : ℕ} (hb : 0 < b) {X : Type} [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    (τ : Representation ℂ (GL (Fin b) k) X) (hτ : IsCuspidal τ)
    (hz : ∀ z ∈ Subgroup.center (GL (Fin b) k), ∃ c : ℂ, ∀ w, τ z w = c • w) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (ρ : Representation ℂ (GL (Fin b) k) Y),
      ρ.IsIrreducible ∧ IsCuspidal ρ ∧ ∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ g (ι v) := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  let S : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
    have hle : Submodule.span ℂ (Set.range fun g => τ g x) ≤
        (Submodule.span ℂ (Set.range fun g => τ g x)).comap (τ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', rfl⟩
      exact Submodule.subset_span ⟨g * g', by simp⟩
    exact hle hv⟩
  have hxS : x ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  have hnt : Nontrivial S.toSubmodule := ⟨⟨⟨x, hxS⟩, 0, fun h => hx (congrArg Subtype.val h)⟩⟩
  obtain ⟨Y, _, _, ρ, hρi, p, hp⟩ := GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep _ _ S.toRepresentation {⟨x, hxS⟩} hnt (by
    refine Submodule.map_injective_of_injective S.toSubmodule.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    show _ = Submodule.span ℂ (Set.range fun g => τ g x)
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨g, v, hv, rfl⟩, rfl⟩
      rw [Finset.mem_singleton.1 hv]
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨_, ⟨g, _, Finset.mem_singleton_self _, rfl⟩, rfl⟩)
  have hρc : IsCuspidal ρ := isCuspidal_of_isSubquotient hτ ⟨S, p, hp⟩
  have hSs : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, Representation.IntertwiningMap.id _, Function.surjective_id⟩ hτ.1
  obtain ⟨ω, hω, hωc⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar hρc.1 hρi
  obtain ⟨ψ, hψ, hψ1⟩ := exists_root_norm hω hb
  have hc' : IsCuspidal (twist ρ (detChar (Fin b) ψ)) := GlobalTheory.LocGL.isCuspidal_twist hρc hψ
  have hsc := GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k b Y _ hc'
  haveI : Nontrivial Y := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρi
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨l, hl, hly⟩ := GlobalTheory.T.exists_smoothDual_ne_zero_at_vector _ _ (twist ρ (detChar (Fin b) ψ)) (fun U hU => by
    obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset (n := Fin b) hU
    exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, GlobalTheory.CentralExponent.isCompact_cong γ hγ, h⟩) hc'.1 y hy
  have hu := GlobalTheory.T.isUnitarisableComplexRep_of_supercuspidal_unitary_center _ _ _ l hl (fun h => hly (by rw [h]; rfl)) (GlobalTheory.LocGL.isIrreducible_twist hρi _) hsc
    (fun z hz => by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨z, rfl⟩ := hz
      have h := GlobalTheory.LocGL.hasCentralChar_twist hωc ψ z
      rw [Fintype.card_fin] at h
      exact ⟨_, hψ1 z, h⟩)
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_nonzero_intertwiningMap_from_unitary_supercuspidal _ _ _ (twist S.toRepresentation (detChar (Fin b) ψ)) _ (twistMap p _)
    (isSmooth_twist hSs hψ.detChar) hsc hu
    (fun z hz' => by
      obtain ⟨c, hc⟩ := hz z hz'
      refine ⟨(detChar (Fin b) ψ z : ℂ) * c, fun w => ?_⟩
      rw [twist_apply, mul_smul]
      exact congrArg _ (Subtype.ext (hc w)))
    (fun h => by
      obtain ⟨w, hw⟩ := hp y
      have h1 : twistMap p (detChar (Fin b) ψ) w = y := hw
      rw [h] at h1
      exact hy h1.symm)
  refine ⟨Y, _, _, ρ, hρi, hρc, S.toSubmodule.subtype ∘ₗ ι.toLinearMap, fun h => hι ?_, fun g v => ?_⟩
  · ext v
    exact LinearMap.congr_fun h v
  · have h1 := Representation.IntertwiningMap.isIntertwining _ _ ι g v
    rw [twist_apply, twist_apply, map_smul] at h1
    exact congrArg Subtype.val (smul_right_injective _ (Units.ne_zero _) h1)

theorem exists_map_jac₂ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hn : 0 < n) :
    ∃ (a b : ℕ) (h : a + b = n) (W W' : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : AddCommGroup W') (_ : Module ℂ W')
      (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W'),
      0 < b ∧ IsSmooth σ ∧ σ.IsIrreducible ∧ IsSmooth ρ ∧ ρ.IsIrreducible ∧ IsCuspidal ρ ∧
      ∃ φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor σ ρ), φ ≠ 0 := by
  classical
  have hex : ∃ b : ℕ, 0 < b ∧ ∃ (a : ℕ) (h : a + b = n), Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) :=
    ⟨n, hn, 0, zero_add n, GlobalTheory.SmGL.JacquetEmptyFirstBlock.jacquet_nontrivial k n V π hi _⟩
  obtain ⟨hb, a, h, hnt⟩ := Nat.find_spec hex
  have hmin := fun t (ht : t < Nat.find hex) => Nat.find_min hex ht
  generalize Nat.find hex = b at hb h hnt hmin
  have hJc := GlobalTheory.T.isCuspidal_jacquetModule_second_block_of_vanishing k a b n h V π hs fun r t h' h0 ht =>
    not_nontrivial_iff_subsingleton.1 fun h1 => hmin t ht ⟨h0, r, h', h1⟩
  obtain ⟨s, hspan⟩ := GlobalTheory.T.normalizedJacquetTwoBlocks_finitelyGenerated k a b n h V π hs hi
  obtain ⟨X, _, _, τ, hτi, f, hf⟩ := GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep _ _ _ s hnt hspan
  have hτs : IsSmooth τ := (IsSubquotient.of_surjective f hf).isSmooth (isSmooth_jac₂ _ hs)
  have hτc : IsCuspidal (k := k) (n := Fin b) (τ.comp (MonoidHom.inr _ _)) :=
    isCuspidal_of_isSubquotient hJc (IsSubquotient.of_surjective (compMap f _) hf)
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτi
  haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin a)
  haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin b)
  obtain ⟨Y, _, _, ρ, hρi, hρc, hι⟩ := exists_irreducible_sub hb (τ.comp (MonoidHom.inr _ _)) hτc fun z hz =>
    GlobalTheory.LocGL.exists_eq_smul_of_isSmooth hτs hτi ⟨τ (1, z), fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (Subgroup.mem_center_iff.1 hz g.2).symm⟩
  obtain ⟨W, _, _, σ, hσs, hσi, ⟨φ⟩⟩ := GlobalTheory.T.exists_equiv_exteriorTensor_of_irreducible_prod_rep _ _ X Y τ ρ hτs hτi hρi
    (GlobalTheory.T.injective_tensor_lift_equivariant_maps_of_irreducible _ X Y (τ.comp (MonoidHom.inr _ _)) ρ hρi (GlobalTheory.LocGL.schur_GL hρc.1 hρi)) hι
  refine ⟨a, b, h, W, Y, _, _, _, _, σ, ρ, hb, hσs, hσi, hρc.1, hρi, hρc, φ.toIntertwiningMap.comp f, fun h0 => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  obtain ⟨w, rfl⟩ := hf x
  have h1 : φ (f w) = 0 := congrArg (fun F => F w) h0
  exact hx ((map_eq_zero_iff φ φ.injective).1 h1)

end GlobalTheory.JacFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthBoundOfRowConditionsAndDualityTheorems
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.InertiaEigenvalues.LengthBoundClosing

theorem stmt_closed : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.Stmt D := by
  intro hA hB hT hE D h51
  exact ⟨GlobalTheory.T.integralityFromMetric_of_designConditionAll hA hB hT hE D h51, Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D⟩

end GlobalTheory.InertiaEigenvalues.LengthBoundClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoeffVanishesOffLevelBadPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCoeff_vanishes_offLevel_badPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t := by
  first | exact @GlobalTheory.BadSuppPf.badSupp | exact GlobalTheory.BadSuppPf.badSupp | (intros; apply GlobalTheory.BadSuppPf.badSupp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicRingEquivAdicCompletionPlaceUnramifiedDegreStatement
section
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_ringEquiv_adicCompletion_place_unramified_degree_one : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) [Fact g.Prime] (w : HeightOneSpectrum (𝓞 E))
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ((g : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 ∧ Formalism.ConjugateSelfDual.normV w = g := by
  first | exact @GlobalTheory.LocalFieldIso.padic_iso_place | exact GlobalTheory.LocalFieldIso.padic_iso_place | (intros; apply GlobalTheory.LocalFieldIso.padic_iso_place <;> assumption)
end

