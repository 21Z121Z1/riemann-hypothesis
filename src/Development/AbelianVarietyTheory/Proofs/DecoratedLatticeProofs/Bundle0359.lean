import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.HalfPairing
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem toMatrix_mem_latRat (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    LinearMap.toMatrix' x ∈ latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) := by
  have hA : D.host.AA = D.host.AA0 := by
    rw [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.ccE, hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S N hN
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    have e : LinearMap.toMatrix' (r • x) = ∑ k, genMap S T r (s' k) (x (s k)) := by
      refine Matrix.ext fun i j => ?_
      have h1 : (Pi.single j 1 : Fin S.rank → D.host.E) = ∑ k, (∑ l, star (s' k l) * S.gram l j) • s k := by
        funext a
        rw [Finset.sum_apply, Pi.single_apply, ← hss a j]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [Matrix.sum_apply, LinearMap.toMatrix'_apply]
      change r * x (Pi.single j 1) i = _
      rw [h1, map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul, genMap, Matrix.of_apply]
      ring
    rw [e]
    exact sum_mem fun k _ => AddSubgroup.subset_closure ⟨r, hA ▸ hr, _, (hs k).2, _, hx _ (hs k).1, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : LinearMap.toMatrix' (c • x) = (c : D.host.E) • LinearMap.toMatrix' x := by
      ext i j; rfl
    rw [e]
    exact smul_mem_latRat c hx

theorem smul_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 E))}
    {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c) {y : Formalism.L2.Col.HomE E a b} (hy : y ∈ halfBO SS M c)
    (Q : HeightOneSpectrum (𝓞 E)) : (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ expS SS Q)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hy Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ expS SS Q)⁻¹ → (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 2 (by field_simp)
  · exact key 0 (by simp)
  · exact key 1 (by simp)

theorem conj_comp_mem (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (h0 : infPart D e = 0) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : Formalism.L2.Col.cO D.host.E s ∉ P.asIdeal := hs
  have hne : Formalism.L2.Col.cO D.host.E s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (by rw [show s = 0 from RingOfIntegers.ext h, map_zero])
  have h1 : finPart D (e * incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h2 := GlobalTheory.PlaceVec.cF_mem_int (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1)
  rw [← GlobalTheory.AdelicLatMove.toEAf_cA, RingHom.map_mul (cA D)] at h2
  have h3 : cA D (incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) = incA D (s : D.host.E)⁻¹ := by
    change incA D (star (star (s : D.host.E))⁻¹) = _
    rw [star_inv₀, star_star]
  rw [h3] at h2
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (GlobalTheory.PlaceVec.finPart_mem_intAE h2) _
    (finTens_mem_latO (one_mem_intAf _) (toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  have h5 := GlobalTheory.PlaceVec.infPart_cA h0
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h5, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem char_sympl_halfB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ u ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), ψ (symplO S T (c • u) (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) = 1 := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc _ _ _ ⟨ΛS, dS, eS⟩ ⟨ΛT, dT, eT⟩ y hy u hu
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hu
  change ψ (symplO S T (c • u) ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r)) = 1
  have hmem : c • ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
    have e1 : c • ((LinearMap.toMatrix' y).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E) • y)).map fun r => cA D (es PP) * incA D r : WO S T) := by
      ext i j
      rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, map_sum, nsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun PP _ => ?_
      change _ = cA D (es PP) * incA D ((c : D.host.E) * LinearMap.toMatrix' y i j)
      rw [RingHom.map_mul (incA D), map_natCast, mul_left_comm]
    rw [e1]
    refine sum_mem fun PP hPP => conj_comp_mem hP.cc dS (hes PP hPP) ?_ (smul_mem_locP hc hy _)
    refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  have h := char_sympl_eq_one hP.std dS dT hu hmem
  rw [← symplHom_apply, map_nsmul] at h
  rw [← symplHom_apply, map_nsmul]
  exact h

end GlobalTheory.AdForm.HalfPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLevelContainsUnitaryNearOne
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped Topology

noncomputable section

namespace GlobalTheory.LevelApprox

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.ColAd

theorem eq_zero_of_le_pow {γ t : WithZero (Multiplicative ℤ)} (hγ : γ < 1) (h : ∀ m : ℕ, t ≤ γ ^ m) : t = 0 := by
  by_contra ht
  by_cases hγ0 : γ = 0
  · have := h 1
    rw [hγ0, pow_one] at this
    exact ht (le_antisymm this zero_le')
  have hg : γ.log < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log hγ0]
    simpa using hγ
  set N : ℕ := (-t.log).toNat + 1 with hN
  have hm : t.log ≤ (N : ℤ) * γ.log := by
    have h3 : WithZero.exp t.log ≤ WithZero.exp (N • γ.log) := by
      rw [WithZero.exp_nsmul, WithZero.exp_log ht, WithZero.exp_log hγ0]
      exact h N
    rw [WithZero.exp_le_exp, nsmul_eq_mul] at h3
    exact h3
  have h1 : (N : ℤ) * γ.log ≤ -(N : ℤ) := by
    have : (0 : ℤ) ≤ (N : ℤ) := by positivity
    nlinarith
  have h2 := Int.self_le_toNat (-t.log)
  have h4 : (N : ℤ) = ((-t.log).toNat : ℤ) + 1 := by rw [hN]; push_cast; ring
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def SmallAt (Q : Finset (HeightOneSpectrum (𝓞 E))) (d : ℕ) : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  {a | (∀ w ∉ Q, adAt F w a = 0) ∧ ∀ w ∈ Q, Valued.v (adAt F w a) ≤ WithZero.exp (-(d : ℤ))}

theorem exists_smallAt_subset (Q : Finset (HeightOneSpectrum (𝓞 E))) {V : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hV : letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      V ∈ 𝓝 (0 : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : ℕ, SmallAt (F := F) Q d ⊆ V := by
  classical
  letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  haveI := Formalism.L2.Col.adeles_t2Space (F := F) (E := E)
  obtain ⟨β, hβ0, hβ⟩ : ∃ β : 𝓞 E, β ≠ 0 ∧ ∀ P ∈ Q, β ∈ P.asIdeal := by
    choose f hf hf0 using fun P : HeightOneSpectrum (𝓞 E) => Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact ⟨∏ P ∈ Q, f P, Finset.prod_ne_zero_iff.2 fun P _ => hf0 P, fun P hP =>
      Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem f hP) (hf P)⟩
  set b : E := algebraMap (𝓞 E) E β with hb
  have hb0 : b ≠ 0 := by simpa [hb] using hβ0
  let ι : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F := Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
  set e : E ⊗[F] FiniteAdeleRing (𝓞 F) F := ∑ P ∈ Q, PtExist.idem F P with he_def
  have he : ∀ w, adAt F w e = if w ∈ Q then 1 else 0 := by
    intro w
    rw [he_def, map_sum]
    simp only [PtExist.adAt_idem]
    exact Finset.sum_ite_eq Q w (fun _ => (1 : w.adicCompletion E))
  have hint : ∀ y ∈ Formalism.L2.Herm.intAf F E, ∀ w, Valued.v (adAt F w y) ≤ 1 := fun y hy w =>
    (mem_rInt_iff F E y).1 hy w
  have hbw : ∀ w ∈ Q, Valued.v (adAt F w (ι b)) < 1 := fun w hw => by
    rw [adAt_inclE, valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 (hβ w hw)
  have hbne : ∀ w, adAt F w (ι b) ≠ 0 := fun w => by
    rw [adAt_inclE]
    exact (map_ne_zero _).2 hb0
  let c : ℕ → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun m => e * ι b ^ m
  let K : ℕ → Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := fun m => (c m * ·) '' (Formalism.L2.Herm.intAf F E : Set _)
  have hKc : ∀ m, IsCompact (K m) := fun m => Formalism.L2.Col.rlt_isCompact_intAf.image (continuous_mul_left (c m))
  have hKa : Antitone K := by
    refine antitone_nat_of_succ_le fun m => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨ι b * y, mul_mem (Formalism.L2.Col.iA_mem β) hy, ?_⟩
    simp only [c, pow_succ]
    ring
  have hK0 : ∀ x ∈ ⋂ m, K m, V ∈ 𝓝 x := by
    intro x hx
    have : x = 0 := by
      refine PtExist.ad_ext fun w => ?_
      rw [map_zero]
      by_cases hw : w ∈ Q
      · have h0 : Valued.v (adAt F w x) = 0 := eq_zero_of_le_pow (hbw w hw) fun m => by
          obtain ⟨y, hy, hxy⟩ := Set.mem_iInter.1 hx m
          rw [← hxy]
          simp only [c, map_mul, map_pow, he, if_pos hw, one_mul]
          exact mul_le_of_le_one_right' (hint y hy w)
        exact (Valuation.zero_iff _).1 h0
      · obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.1 hx 0
        simp only [c, map_mul, he, if_neg hw, zero_mul]
    rw [this]
    exact hV
  obtain ⟨m, hm⟩ := exists_subset_nhds_of_isCompact hKa.directed_ge hKc hK0

  let D : ℕ := ∑ w ∈ Q, (-(Valued.v (adAt F w (ι b))).log).toNat
  have hD : ∀ w ∈ Q, WithZero.exp (-(D : ℤ)) ≤ Valued.v (adAt F w (ι b)) := fun w hw => by
    have h0 : Valued.v (adAt F w (ι b)) ≠ 0 := (Valuation.ne_zero_iff _).2 (hbne w)
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    have h1 : (-(Valued.v (adAt F w (ι b))).log).toNat ≤ D :=
      Finset.single_le_sum (f := fun w => (-(Valued.v (adAt F w (ι b))).log).toNat) (fun _ _ => Nat.zero_le _) hw
    have h2 := Int.self_le_toNat (-(Valued.v (adAt F w (ι b))).log)
    omega
  refine ⟨m * D, fun a ha => hm ?_⟩
  have hinv : ∀ w, adAt F w (ι b⁻¹) = (adAt F w (ι b))⁻¹ := fun w => by
    rw [adAt_inclE, adAt_inclE, map_inv₀]
  refine ⟨e * ι b⁻¹ ^ m * a, (mem_rInt_iff F E _).2 fun w => ?_, ?_⟩
  · show Valued.v (adAt F w _) ≤ 1
    by_cases hw : w ∈ Q
    · simp only [map_mul, map_pow, he, hinv, if_pos hw, one_mul, map_inv₀, inv_pow, map_one]
      have hv : 0 < Valued.v (adAt F w (ι b)) ^ m :=
        pow_pos (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hbne w))) m
      rw [inv_mul_le_one₀ hv]
      refine (ha.2 w hw).trans ?_
      have : WithZero.exp (-((m * D : ℕ) : ℤ)) = WithZero.exp (-(D : ℤ)) ^ m := by
        rw [← WithZero.exp_nsmul]
        congr 1
        push_cast
        ring
      rw [this]
      exact pow_le_pow_left₀ zero_le' (hD w hw) m
    · rw [map_mul, ha.1 w hw, mul_zero, map_zero]
      exact zero_le'
  · refine PtExist.ad_ext fun w => ?_
    simp only [c, map_mul, map_pow, he, hinv]
    by_cases hw : w ∈ Q
    · rw [if_pos hw, one_mul, one_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (hbne w), one_pow, one_mul]
    · rw [ha.1 w hw, mul_zero, mul_zero]

end GlobalTheory.LevelApprox

namespace GlobalTheory.LevelApprox

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.ColAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_entry_sub_one {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (i j : Fin n) :
    adAt F w ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) = (locM w z - 1) i j := by
  rw [map_sub, Matrix.sub_apply]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem entry_mem_smallAt {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} {d : ℕ}
    {z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h1 : ∀ w ∉ Q, locM w z = 1)
    (h2 : ∀ w ∈ Q, Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z - 1)) (i j : Fin n) :
    (z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j ∈ SmallAt (F := F) Q d := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [adAt_entry_sub_one, h1 w hw, sub_self, Matrix.zero_apply]
  · rw [adAt_entry_sub_one]
    exact h2 w hw i j

theorem mem_U_of_near_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad)
    (Q : Finset (HeightOneSpectrum (𝓞 E))), ∃ d : ℕ, ∀ z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    z ∈ Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ w ∉ Q, GlobalTheory.Mem.ColAd.locM w z = 1) →
    (∀ w ∈ Q, GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z - 1) ∧
      GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z⁻¹ - 1)) → z ∈ S.U := by
  intro F E _ _ _ _ _ σ n J T f bad S Q
  classical
  letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  let A : ℕ → Set (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := fun d => {z | (∀ w ∉ Q, locM w z = 1) ∧
    ∀ w ∈ Q, Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z - 1) ∧ Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z⁻¹ - 1)}
  have hexp : Antitone fun d : ℕ => WithZero.exp (-(d : ℤ)) := fun a b h =>
    WithZero.exp_le_exp.2 (by simpa using h)
  have hA : Antitone A := fun a b h z hz => ⟨hz.1, fun w hw => ⟨(hz.2 w hw).1.mono (hexp h), (hz.2 w hw).2.mono (hexp h)⟩⟩
  have hinv1 : ∀ z ∈ A 0, ∀ w ∉ Q, locM w z⁻¹ = 1 := fun z hz w hw => by
    have := locM_mul (P := w) z z⁻¹
    rw [mul_inv_cancel, locM_one, hz.1 w hw, one_mul] at this
    exact this.symm
  let G : Filter (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := ⨅ d, Filter.principal (A d)
  have hsmall : ∀ g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ d, ∀ z ∈ A d, g z ∈ SmallAt (F := F) Q d) → Filter.Tendsto g G (𝓝 0) := fun g hg V hV => by
    obtain ⟨d, hd⟩ := exists_smallAt_subset (F := F) Q hV
    exact Filter.mem_iInf_of_mem d (Filter.mem_principal.2 fun z hz => hd (hg d z hz))
  have hentry : ∀ (M : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) → Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      (∀ i j, Filter.Tendsto (fun z => M z i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) G (𝓝 0)) →
      Filter.Tendsto M G (𝓝 1) := fun M hM =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => by
      have := (hM i j).add_const ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j)
      simpa using this
  have hT : Filter.Tendsto id G (𝓝 (1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Filter.Tendsto.prodMk_nhds ?_ ((MulOpposite.continuous_op.tendsto _).comp ?_)
    · refine hentry _ fun i j => hsmall _ fun d z hz => entry_mem_smallAt hz.1 (fun w hw => (hz.2 w hw).1) i j
    · refine hentry (fun z => ((z⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) fun i j => hsmall _ fun d z hz => ?_
      exact entry_mem_smallAt (fun w hw => hinv1 z (hA (Nat.zero_le d) hz) w hw) (fun w hw => (hz.2 w hw).2) i j
  have h1 : {x : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ S.U} ∈
      𝓝 (1 : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) := S.U_open.mem_nhds S.U.one_mem
  obtain ⟨t, ht, hts⟩ := (mem_nhds_subtype _ _ _).1 h1
  have hdir : Directed (· ≥ ·) fun d => Filter.principal (A d) :=
    Antitone.directed_ge (f := fun d => Filter.principal (A d)) fun a b h => Filter.principal_mono.2 (hA h)
  obtain ⟨d, hd⟩ := (Filter.mem_iInf_of_directed hdir _).1 (hT ht)
  exact ⟨d, fun z hz h1 h2 => hts (show (⟨z, hz⟩ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∈ Subtype.val ⁻¹' t from
    hd ⟨h1, h2⟩)⟩

end GlobalTheory.LevelApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopOnto

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.Top.Model GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice Matrix

section General

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ)))).mul (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  obtain ⟨u, rfl⟩ : IsUnit g := isUnit_of_mul_isUnit_right (hg'.symm ▸ hG : IsUnit (gᴴ * gramAt D V τ * g))
  exact Submodule.subset_span
    (Formalism.IndefR.SchurOrthogonalityAlt.smoothVec_rep M τ ⟨u, hg⟩ (Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_of_mem hw))

theorem real_induction (hθ : IsInfFam θ) (P : GA D V → Prop) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hat : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P (atTau θ V τ g)) : ∀ a ∈ GinfC V, P a := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have key : ∀ s : Finset D.what₂.Tau, ∀ a ∈ GinfC V, (∀ τ ∉ s, infMat D.sp.cm.sig V.gram (θ τ) a = 1) → P a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha h
      rw [R.2.2.1 a ha 1 (one_mem _) fun τ => by rw [h τ (Finset.notMem_empty τ), infMat_one]]
      exact h1
    | insert τ s hτ ih =>
      intro a ha h
      have hg := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
      have hb := atTau_spec hθ V τ hg
      have hi : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a))⁻¹ *
          infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) = 1 := fun ρ => by
        rw [← infMat_mul, inv_mul_cancel, infMat_one]
      rw [← mul_inv_cancel_left (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) a]
      refine hmul _ _ (hat τ _ hg) (ih _ (mul_mem (inv_mem hb.1) ha) fun ρ hρ => ?_)
      rw [infMat_mul]
      by_cases c : ρ = τ
      · subst c
        have := hi ρ
        rwa [hb.2.1] at this
      · have := hi ρ
        rw [hb.2.2 ρ c] at this
        rw [h ρ (by simp [c, hρ])]
        exact this
  exact fun a ha => key Finset.univ a ha fun τ h => absurd (Finset.mem_univ τ) h

theorem multT_rel {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (v v' : M.Vec) (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → m v' x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) :
    T (PiTensorProduct.tprod ℂ v') x' = c * T (PiTensorProduct.tprod ℂ v) x := by
  obtain ⟨m, hm, rfl⟩ := hT
  show PiTensorProduct.lift m _ x' = c * PiTensorProduct.lift m _ x
  rw [PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
  induction hm using Submodule.span_induction with
  | mem m hm => exact h m hm
  | zero => simp
  | add a b _ _ ha hb => simp only [MultilinearMap.add_apply, Pi.add_apply, ha, hb, mul_add]
  | smul r a _ ha => simp only [MultilinearMap.smul_apply, Pi.smul_apply, ha, smul_eq_mul]; ring

theorem multT_rel' {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → ∀ v, m v x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) (v : SmT M) :
    T v x' = c * T v x := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, multT_rel v v x x' c (fun m hm => h m hm v) hT, smul_eq_mul, smul_eq_mul]
    ring
  | add a b ha hb => rw [map_add, Pi.add_apply, Pi.add_apply, ha, hb, mul_add]

theorem exists_ratPt (hθ : IsInfFam θ) {n : ℕ} (hn : V.rank = n) (δ : GL (Fin n) D.host.E)
    (hδ : δ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))) :
    ∃ γ ∈ GQ V, finN V hn γ = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ ∧
      ∀ τ, (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) = (δ : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) := by
  subst hn
  have hm : Formalism.UG.bc (incA D) δ ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram :=
    unit_transfer (Equiv.refl _) (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig)
      (fun _ => rfl) V.gram _ (fun _ _ => rfl) δ.1 _ (fun _ _ => rfl) hδ
  refine ⟨⟨_, hm⟩, ⟨δ, hδ, rfl⟩, rfl, fun τ => ?_⟩
  exact Matrix.ext fun i j => (hθ τ).1 _

theorem infN_eq {n : ℕ} (hn : V.rank = n) (γ : GA D V) (τ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) =
      (infMat D.sp.cm.sig V.gram (θ τ) γ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

end General

section Law

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

set_option maxHeartbeats 1000000 in

theorem real_translate (hθ : IsInfFam θ) (hj : IsJ u M j) : ∀ a ∈ GinfC D.sp.X', ∀ v : SmT M, ∃ v' : SmT M,
    lT _ (infPt θ a) (j v') = j v ∧ ∀ T ∈ MultT θ M J χ, ∀ h, T v' h = T v (h * a) := by
  refine real_induction hθ _ (fun v => ⟨v, by rw [map_one, lT_one], fun T _ h => by rw [mul_one]⟩) (fun a b ha hb v => ?_)
    fun τ g hg v => ?_
  · obtain ⟨v₁, e1, f1⟩ := hb v
    obtain ⟨v₂, e2, f2⟩ := ha v₁
    refine ⟨v₂, by rw [map_mul (infPt θ), lT_mul, e2, e1], fun T hT h => ?_⟩
    rw [f2 T hT, f1 T hT, mul_assoc]
  · induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      let w : M.sm τ := ⟨M.rep τ g (v τ), rep_mem_sm M τ hg _ (v τ).2⟩
      refine ⟨r • PiTensorProduct.tprod ℂ (Function.update v τ w), ?_, fun T hT h => ?_⟩
      · rw [map_smul, map_smul, map_smul]
        congr 1
        funext y
        refine hj.eqv τ g hg v w rfl _ y fun ρ => ?_
        refine (congrArg (· * y.1 ρ) (infN_atTau θ _ (rankP D) hθ τ hg ρ)).trans ?_
        by_cases c : ρ = τ
        · subst c
          simp only [Function.update_self]
        · simp only [Function.update_of_ne c, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      · rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
          multT_rel v (Function.update v τ w) (h * atTau θ _ τ g) h 1 (fun m hm => by
            rw [one_mul]; exact congrFun (hm.equiv τ g hg v w rfl) h) hT, one_mul]
    | add a b ha hb =>
      obtain ⟨a', e1, f1⟩ := ha
      obtain ⟨b', e2, f2⟩ := hb
      refine ⟨a' + b', by rw [j.map_add, j.map_add, LinearMap.map_add, e1, e2], fun T hT h => ?_⟩
      rw [T.map_add, T.map_add, Pi.add_apply, Pi.add_apply, f1 T hT, f2 T hT]

theorem hasMat_finPt {h : GA D D.sp.X'} (hh : h ∈ GfC D.sp.X') : HasMat h (finPt h).1 :=
  ⟨hh, fun i j => (finN_apply D.sp.X' (rankP D) h (finCongr (rankP D) i) (finCongr (rankP D) j)).symm⟩

end Law

section Form

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

end Form

end GlobalTheory.Core.Rk.TopOnto

end
end

