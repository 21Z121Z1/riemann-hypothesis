import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.TransW
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalD
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0015
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0101
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntSExpMulTranslate
section
noncomputable section

open scoped BigOperators
open Formalism.L2.Th1
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.L2.Th1.D (normInt)
open Formalism.G (unitBall)

namespace GlobalTheory.ThLoc

theorem endoDatum_of_model (d : ℕ) (L : PeriodPair) (hmod : d % 4 = 3) (hCM : HasCMBy d L)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (W : WeierstrassCurve ℂ_[p]) (hU : Unif p L ι W)
    (hW : IntCurve W) (m n : ℤ) (hN : ¬ (p : ℤ) ∣ normInt d m n) :
    ∃ (S : Finset ℂ) (neg : S → S) (xP yP : S → ℂ_[p]),
      C.IsEndoCurve W neg xP yP (ι ((m : ℂ) + (n : ℂ) * omegaK d)) ∧
      (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
      ι ((m : ℂ) + (n : ℂ) * omegaK d) * ι ((m : ℂ) + (n : ℂ) * (1 - omegaK d)) =
        (Fintype.card S : ℂ_[p]) + 1 ∧
      ι ((m : ℂ) + (n : ℂ) * omegaK d) *
          (ι ((m : ℂ) + (n : ℂ) * omegaK d) - ι ((m : ℂ) + (n : ℂ) * (1 - omegaK d))) *
          ι (F.s2 L) = ∑ P, (xP P + W.b₂ / 12) := by
  have hN0 : normInt d m n ≠ 0 := by
    intro h
    apply hN
    rw [h]
    exact dvd_zero _
  obtain ⟨S, neg, hcard, hker, hnegP, hE, hprod, hs2C⟩ := D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0
  have hpN : ¬ p ∣ (S.card + 1) := by
    intro h
    apply hN
    rw [← hcard]
    exact_mod_cast h
  have hpt : ∀ P : S, E.ptW p L ι W (P : ℂ) =
      .some _ _ (E.AnaSysW.nonsing hU (P : ℂ) (hker P).2) := by
    intro P
    unfold E.ptW
    rw [dif_pos ⟨(hker P).2, E.AnaSysW.nonsing hU (P : ℂ) (hker P).2⟩]
  have hint : ∀ P : S, ‖E.AnaSysW.xc p L ι W P‖ ≤ 1 ∧ ‖E.AnaSysW.yc p L ι W P‖ ≤ 1 := by
    intro P
    have h := E.TransW.ptW_int E.analytic_point_map_add E.analytic_point_eq_zero_iff hU hW (P : ℂ) (S.card + 1) hpN
      (hker P).1 (hker P).2
    rw [hpt P] at h
    exact h
  refine ⟨S, neg, fun P => E.AnaSysW.xc p L ι W P, fun P => E.AnaSysW.yc p L ι W P,
    ?_, fun P => (hint P).1, fun P => (hint P).2, ?_, ?_⟩
  · apply D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) W
      (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    · intro P
      exact (E.AnaSysW.nonsing hU (P : ℂ) (hker P).2).1
    · intro P
      constructor
      · simp only [E.AnaSysW.xc, (hnegP P).1]
      · simp only [WeierstrassCurve.Affine.negY, E.AnaSysW.xc, E.AnaSysW.yc]
        rw [(hnegP P).2, (hnegP P).1, map_neg]
        ring
    · have h := D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE
      simp only [PowerSeries.map_id, RingHom.id_apply, E.AnaSysW.xc, sub_add_cancel]
      rw [E.weierstrass_series_eq_transported p L ι W hU]
      exact h
  · rw [← map_mul, hprod, Fintype.card_coe]
    simp
  · rw [← map_sub, ← map_mul, ← map_mul, hs2C, map_sum]
    simp [E.AnaSysW.xc]

theorem jets_phW_three (d : ℕ) (L : PeriodPair) (hmod : d % 4 = 3) (h3 : d % 3 = 2) (hCM : HasCMBy d L)
    (ι : ℂ ≃+* ℂ_[3]) (W : WeierstrassCurve ℂ_[3]) (hU : Unif 3 L ι W) (hW : IntCurve W)
    (i : ℕ) (hi : 1 ≤ i) : ‖C.jet (logSer W) (E.phW 3 L ι W) i‖ ≤ 1 := by
  have hnorm : normInt d (-1) 2 = d := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℤ) + 1 = 4 * k := ⟨((d : ℤ) + 1) / 4, by omega⟩
    have hdiv : ((d : ℤ) + 1) / 4 = k := by omega
    unfold normInt
    rw [hdiv]
    linear_combination -hk
  have hN : ¬ ((3 : ℕ) : ℤ) ∣ normInt d (-1) 2 := by
    rw [hnorm]
    omega
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩ :=
    endoDatum_of_model d L hmod hCM 3 ι W hU hW (-1) 2 hN
  set al := ι (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) with hal
  set albar := ι (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * (1 - omegaK d)) with halbar
  have hsum : al + albar = ((0 : ℤ) : ℂ_[3]) := by
    rw [hal, halbar, ← map_add]
    have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) +
        (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * (1 - omegaK d)) = 0 := by
      push_cast
      ring
    rw [e]
    simp
  have hsq : al ^ 2 = -(d : ℂ_[3]) := by
    rw [hal, ← map_pow]
    have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) ^ 2 = -(d : ℂ) := by
      push_cast
      linear_combination 4 * D.CurveNormEndomorphisms.omega_sq d
    rw [e, map_neg, map_natCast]
  have h2 : ‖(2 : ℂ_[3])‖ = 1 := Top.OrthogonalGaussModelNormLemmas.norm_two 3 (by norm_num)
  have hal1 : ‖al‖ = 1 := by
    have h1 := congrArg norm hsq
    rw [norm_pow, norm_neg, E.ScaledModelNorms.norm_nat 3 (show ¬ 3 ∣ d by omega)] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  have hdiff : ‖al - albar‖ = 1 := by
    have e : al - albar = 2 * al := by
      have := hsum
      push_cast at this
      linear_combination -this
    rw [e, norm_mul, h2, hal1, one_mul]
  have hb : ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 3 * k := ⟨(d + 1) / 3, by omega⟩
    have hk' : (d : ℂ_[3]) + 1 = 3 * (k : ℂ_[3]) := by exact_mod_cast hk
    have e : (al ^ 2 - 1) * (W.b₂ / 12) = -((k : ℂ_[3]) * W.b₂) / 2 ^ 2 := by
      rw [hsq]
      linear_combination (-W.b₂ / 12) * hk'
    have hb2 : ‖W.b₂‖ ≤ 1 := by
      have hm : W.b₂ ∈ unitBall ℂ_[3] := by
        obtain ⟨a1, a2, -⟩ := Top.OrthogonalGaussModelNormLemmas.coeffIn hW
        unfold WeierstrassCurve.b₂
        exact add_mem (pow_mem a1 2) (mul_mem (ofNat_mem _ 4) a2)
      exact hm
    rw [e, norm_div, norm_pow, h2, one_pow, div_one, norm_neg, norm_mul]
    exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one _ k) (norm_nonneg _) hb2
  have h := G.curveJetsUnramThm ℂ_[3] W (Top.OrthogonalGaussModelNormLemmas.coeffIn hW) h2 (ι (F.s2 L)) al albar 0 S neg xP yP
    hE hx hy hprod hal1 hsum hdiff hb hs i hi
  unfold E.phW
  rw [← E.weierstrass_series_eq_transported 3 L ι W hU]
  exact h

theorem intS_exp_mul_translate (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p])
    (W : WeierstrassCurve ℂ_[p]) (hU : Unif p L ι W) (hW : IntCurve W) (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice)
    (hω2 : ω₀ / 2 ∉ L.lattice) (s : ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ p ∣ N)
    (hNs : (N : ℂ) * s ∈ L.lattice) :
    E.IntS (B.fExp (E.phW p L ι W) * E.inW p ι W (F.opU L s (F.th0 L (ω₀ / 2)))) := by
  have hl2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have h2t : ((2 : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by simpa using E.TransW.half_mem hω 1
  obtain ⟨hc1, -⟩ := E.analytic_translate_model p L ι W hU hW (ω₀ / 2) 2 (by norm_num) hl2' h2t hω2
  have hN2 : ¬ p ∣ 2 * N := fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim hl2' hlN
  have m3 : ((2 * N : ℕ) : ℂ) * (s + ω₀ / 2) ∈ L.lattice := by
    rw [mul_add]
    exact add_mem (E.TransW.two_mem hNs) (E.TransW.half_mem hω N)
  have hsim := (E.TransW.hW_sim p L ι W (ω₀ / 2) s (2 * N) (by omega) (E.TransW.two_mem hNs)
    (E.TransW.half_mem hω N) hω2).mul_left (B.fExp (E.phW p L ι W))
  refine (hsim.gaussOne ?_).1
  rw [mul_left_comm, ← E.TransW.gW_eq]
  exact E.Tor.gaussOne_C_mul (by rw [norm_inv, hc1, inv_one])
    (E.TransW.gW_gauss E.analytic_translate_system_model E.analytic_point_map_add E.analytic_point_eq_zero_iff hU hW _ (2 * N) hN2 m3)

theorem thetaZJetsThree : ThetaZJetsThree := by
  intro d L hd8 hd3 hCM ι W hU hW ω₀ hω h1 _ n _ κ _ r s N hr hN h3N hs
  have hω2 : ω₀ / 2 ∉ L.lattice := fun h => h1 (hCM _ h)
  obtain ⟨hlp, -, -, -, hu⟩ := C.curveFrame ℂ_[3] (unitBall ℂ_[3]) W (Top.OrthogonalGaussModelNormLemmas.coeffIn hW)
  have hph : PowerSeries.constantCoeff (E.phW 3 L ι W) = 0 := E.AnaSysW.cc_phW 3 L ι W
  obtain ⟨e1, hInt⟩ := E.prodInt ℂ_[3] κ n (E.phW 3 L ι W) r
    (fun k i => B.fExp (E.phW 3 L ι W) * E.inW 3 ι W (F.opU L (s k i) (F.th0 L (ω₀ / 2))))
    hph hr (fun k i => intS_exp_mul_translate 3 (by norm_num) L ι W hU hW ω₀ hω hω2 (s k i) N hN h3N
      (hs k i))
  have key := (G.kernelTwo ℂ_[3] _ _ _ hlp hu hph
    (jets_phW_three d L (by omega) hd3 hCM ι W hU hW) n (fun _ => 1) (fun _ => by simp) _
    (fun m => hInt m)).1
  obtain ⟨hl0, -, hv0, -, hlv⟩ := hlp
  rw [Top.KJ.phSum_one] at key
  change Formalism.DworkPowerSeriesWeights.JetsIntegral (G.toZ _ (Formalism.DworkPowerSeriesWeights.mvExp _ * _)) at key
  rw [← e1, Top.KJ.toZ_thetaProd hv0] at key
  convert key using 1
  unfold Top.thetaZ
  congr 1
  funext k i
  change _ = PowerSeries.subst _ (B.fExp (-(E.phW 3 L ι W)) * _)
  rw [← mul_assoc, ← B.fExp_add (by rw [map_neg]; exact neg_eq_zero.2 hph) hph,
    neg_add_cancel, B.ParO.fExp_zero, one_mul]
  unfold E.inW
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hv0), hlv]
  exact (PowerSeries.X_subst _).symm

end GlobalTheory.ThLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
section
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

section Notions

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] {a b : ℕ}

def AwayAt (P : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)) (B : ℕ) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) : Prop :=
  (∀ x, w.valuation K (Φ x) ≤ 1) ∧ ∀ x z, z ∈ homAt {P} N N' → Φ (x + ((qOf P : E) ^ B) • z) = Φ x

open Classical in

def DatumAt (Sg S : Finset (HeightOneSpectrum (𝓞 E))) (g c : ℕ) (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, w.valuation K (Ξ x) ≤ 1) ∧ (∀ x, Ξ x ≠ 0 → x ∈ homAt Sg N N') ∧
    ∀ x z, z ∈ mulLat g (homAt Sg N N') → z ∈ mulLat c (homAt (S \ Sg) N N') → Ξ (x + z) = Ξ x

end Notions

def JetLossAt {X : Fields} (Pr : Primes X) (R : Ranks) (A : Amb X)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) : Prop :=
  ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
  ∀ (u : Pr.Word) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok →
  ∀ (j b : ℕ), j < R.m → b = R.N (j + 1) →
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → StdOver (Pr.g i) N → StdOver (Pr.g i) N' →
  ∀ Ξ : HomE X.E (R.N j) b → X.K, DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w N N' Ξ →
  ∀ e : DVar X.Tau (R.N j) b →₀ ℕ, e.degree + 1 < Pr.g i →
    e ∈ RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ →
    w.valuation X.K ((Pr.g i : X.K) ^ (X.f * R.N j * b) *
      (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) *
      jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ e) ≤ 1

def JetLoss (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  HostTie EX → IsSel (recFields D) sel → AnTie D δ χ cD →
    JetLossAt (recPrimes EX) D.R (ambOf (recSeam D) B χ cD) sel (badS D)

def LevelPrimes : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel →
    ∀ P : rowSG Pr sel mu, DegOneUnram P.1 ∧ (P.1 ∉ Pr.vGs → qOf P.1 ∉ S)

def HeckeUnit : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (e : X.Tau → ℚ) (j : Fin m)
    (χ : Formalism.L2.Host.HChar X.E), X.Ok → Pr.Ok → IsMu0 Ch σ₀ e j χ →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : HeightOneSpectrum (𝓞 X.E)), p.Prime → (p : 𝓞 X.K) ∈ w.asIdeal →
      (p : 𝓞 X.E) ∉ P.asIdeal → ∀ (x : X.Eˣ) (k : X.K), σ₀ k = ((χ.locK P x : ℂˣ) : ℂ) → w.valuation X.K k = 1

def TwistUnit : Prop :=
  ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K] [NumberField K] (S : Set ℕ)
    (mu : Tup F E K S) (P : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)),
    w.valuation K ((unifVal (mu : Chr F E K) P : Kˣ) : K) = 1 ∧ w.valuation K ((qValC (mu : Chr F E K) P : Kˣ) : K) = 1

def ScalarUnit : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (e : Fin R.m → X.Tau → ℚ) (eta : Formalism.L2.Host.HChar X.E),
    X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → Ch.Tied G.σ₀ e G.mu0 eta → L.Ok Ch sel mu cst G m2 →
    ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ∀ j, j < R.m →
      (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vG i → w.valuation X.K (cst.muq (j + 1) P) = 1) ∧
      ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
        IsSdLat N → StdOver (Pr.g i) N → IsFrames N fr →
        w.valuation X.K (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr) = 1

def EntryAtG : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    L.Ok Ch sel mu cst G m2 → ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
      DegOneUnram P.1 → FnMod P.1 (XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P))

def VolumeAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j)
    (w : HeightOneSpectrum (𝓞 X.K)), P ∉ Pr.vGs → DegOneUnram P → ((qOf P : ℕ) : 𝓞 X.K) ∉ w.asIdeal →
    w.valuation X.K (Loc.volN X.K (Loc.Cbe (Jat (Pr := Pr) sharp j P) h)
      (Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P)))⁻¹ ≤ 1

def EntryAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → DegOneUnram P.1 →
      ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal → (∀ j, j < R.m → w.valuation X.K (cst.muq (j + 1) P) = 1) →
      (∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)),
        AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _) (XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P))) ∧
      ∀ (al : L.β m2) (y : Sp X.E (R.N (m2 + 1))),
        AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _) fun x => PsiAt Ch sel mu cst m2 P (L.h m2 al P) x y

def TopAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (u : Pr.Word), Pr.Ok → IsSel X sel → Pr.T u ∈ S →
    L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → DegOneUnram P.1 →
      ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal →
      ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
        AwayAt P.1 w cst.B p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P)

def JetOpIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K)),
      LatWithBasis w M 1 → LatWithBasis w MW 1 →
      ∀ (c : K) (J : (DVar ι a b →₀ ℕ) → K), (∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) →
        ∀ F ∈ HAt w lam M, c • jetOp lam lam' J n F ∈ HAt w lam' MW

def NabLeDel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → (∀ τ, (lam τ).spread < p) →
      localization₂ w.asIdeal (nabK lam M) ≤ localization₂ w.asIdeal (delK lam M)

open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.ColPeriod.N_lt_succ (R : _root_.Formalism.BasicNotions.Ranks) (j : ℕ) : R.N j < R.N (j + 1) := by
  unfold _root_.Formalism.BasicNotions.Ranks.N
  simp

def ChainWeights : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (u : Pr.Word) (j : ℕ), j < R.m →
    ∃ s s' : X.Tau → ℤ, WtCompat (N_lt_succ R j) (W.lamTrue u j) (W.lamTrue u (j + 1)) s s' (nuLast W u j) ∧
      ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a

def PartitionSize : Prop :=
  ∀ (D : D7) (EX : ErrX D) (u : D.what₂.Word) (j : ℕ), j < D.R.m → ∀ τ : D.what₂.Tau,
    nuAbs D u (j + 1) τ = ((∑ a, ((recWts EX).nuW u (j + 1) τ).w a : ℤ) : ℝ)

def StdMove : Prop :=
  ∀ (X : Fields) (Pr : Primes X), Pr.Ok → ∀ (i : Fin 2) (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N →
    ∃ γ : UF X.E n, StdOver (Pr.g i) (gmap γ.1 N)

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationUnimodularCompanionEq
section
open NumberField Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F

noncomputable section

namespace GlobalTheory.CompanLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem locS_mono {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) {M M₁ : Submodule (𝓞 E) W}
    (h : M ≤ M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem le_locS {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) (M : Submodule (𝓞 E) W) :
    M ≤ Formalism.HermitianLatticesTheory.locS S M := fun x hx => ⟨1, S.one_mem, by simpa using hx⟩

theorem locS_le_of_le {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) {M M₁ : Submodule (𝓞 E) W}
    (h : M ≤ Formalism.HermitianLatticesTheory.locS S M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hx'⟩ := h hx
  refine ⟨t * s, S.mul_mem ht hs, ?_⟩
  rw [mul_smul]
  exact hx'

abbrev conjO : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

theorem conjO_mem_hcompl (Q : Ideal (𝓞 E)) {s : 𝓞 E} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q) :
    conjO s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q := by
  have hle : Formalism.HermitianLatticesTheory.hcompl (K := E) Q ≤ (Formalism.HermitianLatticesTheory.hcompl (K := E) Q).comap (conjO (E := E)).toMonoidHom := by
    unfold Formalism.HermitianLatticesTheory.hcompl
    rw [Submonoid.closure_le]
    rintro s ⟨hs1, hs2⟩
    apply Submonoid.subset_closure
    refine ⟨?_, ?_⟩
    · exact hs2 _ rfl
    · intro t ht hm
      have : t = s := by
        apply RingOfIntegers.ext
        have h1 : (t : E) = star (star (s : E)) := ht
        simpa using h1
      exact hs1 (this ▸ hm)
  exact hle hs

theorem hform_smul_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (c : E) (x y : Fin N → E) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hform_smul_right {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (c : E) (x y : Fin N → E) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem hform_add_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (x x' y : Fin N → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  unfold Formalism.UG.hform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, map_add]
  ring

theorem hform_zero_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (y : Fin N → E) :
    Formalism.UG.hform σ J 0 y = 0 := by
  unfold Formalism.UG.hform
  simp

example {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ Formalism.BasicNotions.dualSet σ J L ↔ ∀ x ∈ L, Formalism.UG.hform σ J x y ∈ (algebraMap (𝓞 E) E).range := Iff.rfl

theorem smul_coe {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (c : 𝓞 E) (w : W) :
    c • w = (c : E) • w := (algebraMap_smul E c w).symm

theorem span_dual_le {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E))
    (hfg : Λ₁.FG) (h : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ) :
    Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (starRingEnd E) J Λ) ≤
      Formalism.HermitianLatticesTheory.loc (K := E) Q (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (starRingEnd E) J Λ₁)) := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  have hg : ∀ g ∈ s, ∃ t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q, t • g ∈ Λ := fun g hg => h (Submodule.subset_span hg)
  choose t ht hts using hg
  set u : 𝓞 E := ∏ g ∈ s.attach, conjO (t g.1 g.2) with hu
  have hu_mem : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q :=
    Submonoid.prod_mem _ fun g _ => conjO_mem_hcompl Q (ht g.1 g.2)
  rw [Submodule.span_le]
  intro y hy
  refine ⟨u, hu_mem, Submodule.subset_span ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hgs =>
    rw [smul_coe, hform_smul_right]
    have e : u = (∏ g' ∈ s.attach.erase ⟨g, hgs⟩, conjO (t g'.1 g'.2)) * conjO (t g hgs) := by
      rw [hu]
      exact (Finset.prod_erase_mul _ _ (Finset.mem_attach _ _)).symm
    have h2 : Formalism.UG.hform (starRingEnd E) J (t g hgs • g) y ∈ (algebraMap (𝓞 E) E).range := hy _ (hts g hgs)
    rw [smul_coe, hform_smul_left] at h2
    rw [e, show ∀ A B : 𝓞 E, ((A * B : 𝓞 E) : E) = (A : E) * (B : E) from fun _ _ => rfl, mul_assoc]
    refine Subring.mul_mem _ ⟨_, rfl⟩ ?_
    exact h2
  | zero => rw [hform_zero_left]; exact Subring.zero_mem _
  | add x x' _ _ hx hx' => rw [hform_add_left]; exact Subring.add_mem _ hx hx'
  | smul c x _ hx =>
    rw [smul_coe, hform_smul_left]
    exact Subring.mul_mem _ ⟨conjO c, rfl⟩ hx

theorem compan_le_loc {R : Ranks} {F : Type} [Field F] [NumberField F] [Algebra F E] (sp : Spaces R F E) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)) (hfg : Λ₁.FG)
    (h : Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁) (h₁ : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ) :
    compan (sp := sp) J a Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  have hσ : (sp.cm.sig : E →+* E) = starRingEnd E := RingHom.ext fun _ => rfl
  unfold compan
  rw [hσ]
  apply sup_le
  · exact h.trans (locS_mono _ le_sup_left)
  · rw [Submodule.smul_le]
    intro r hr n hn
    obtain ⟨s, hs, hsn⟩ := span_dual_le J Q Λ Λ₁ hfg h₁ hn
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsn)

end GlobalTheory.CompanLoc

namespace GlobalTheory

theorem loc_compan_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)),
    Λ.FG → Λ₁.FG → Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ →
    Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  intro R F E _ _ _ _ _ _ sp N J a Q Λ Λ₁ hfg hfg₁ h
  have h1 : Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ := (CompanLoc.le_locS _ Λ).trans h.le
  have h2 : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ := (CompanLoc.le_locS _ Λ₁).trans h.ge
  exact le_antisymm (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ Λ₁ hfg₁ h1 h2))
    (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ₁ Λ hfg h2 h1))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDatumFrobeniusRestrictHostFieldStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodDatum_frobenius_restrict_hostField : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (c : D.host.E →+* ↥K.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → ∀ (x : D.host.E) (y : ↥(K0 K)), algebraMap ↥(K0 K) ↥K.1 y = c x → algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y) = c (D.host.sigmaOf (DV.frobG D l) x) := by
  first | exact @GlobalTheory.FrobPeriod.periodFrob_restrict | exact GlobalTheory.FrobPeriod.periodFrob_restrict | (intros; apply GlobalTheory.FrobPeriod.periodFrob_restrict <;> assumption)
end

