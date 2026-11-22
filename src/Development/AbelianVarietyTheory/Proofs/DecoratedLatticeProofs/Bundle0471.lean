import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0377
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0449
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0378
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0454
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroApproximationTwistPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ApproxZero

section Support
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_K1_element_local_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → ∀ c : ℕ, ∃ z ∈ K1 hc n ST SG, (∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 z - 1)) ∧ (∀ w, w ∉ Q → conjPrime₂ w ∉ Q → locM w z = 1) ∧ ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * z) p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ g hg c
  classical
  have hcc : ∀ P : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ P) = P := fun P => by
    ext b
    rw [mem_conjP, mem_conjP, cO_cO]
  obtain ⟨p, hp⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc c hg
  have hN : Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) = p.deco.1.N := congrArg Deco.N hp.deco
  obtain ⟨g', hg', c1, c2, c3⟩ := PtExist.exists_modify (fun P hP => (hQ P hP).2.2.2.2) hg (ptFr p)
    fun P _ => hN ▸ isFr_ptFr p P
  have hoff : ∀ P, P ∈ ST ∨ P ∈ SG → P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hP with hP | hP
      · exact (hQ P h).1 hP
      · exact (hQ P h).2.1 hP
    · have := hQ _ h
      rw [hcc] at this
      rcases hP with hP | hP
      · exact this.2.2.1 hP
      · exact this.2.2.2.1 hP
  have hpt : IsPtOf hc g' p := by
    refine ⟨hg', hN ▸ c1, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
    · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
      rw [← hN] at hv
      have ho := hoff P.1 (Or.inl P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv), e]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [← hN] at hv
      have ho := hoff P.1 (Or.inr P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv)]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [c2 _ P.2, ptFr_of_mem p (hQ P.1 P.2).2.1 P.2]
      rfl
  have hd : decoRaw ST SG g = decoRaw ST SG g' := hp.deco.trans (near_of_isPtOf hpt c).deco.symm
  refine ⟨g⁻¹ * g', mem_principal_of_same_decoration hc n ST SG hg hg' hd, fun P => ?_, fun w h1 h2 => ?_, p, by rwa [mul_inv_cancel_left]⟩
  · have e : locM P.1 g' = ratM P.1 (p.fr P) := Matrix.ext fun i j => hpt.fr P i j
    rw [locM_mul, e]
    exact hp.fr P
  · have hinv : locM w g'⁻¹ = locM w g⁻¹ := by
      refine Matrix.ext fun i j => ?_
      have := c3 w h1 h2 (Pi.single j 1) i
      simpa [GlobalTheory.Mem.Col2.pullV, Formalism.L2.Col.pullV, Matrix.mulVec, dotProduct, Pi.single_apply, locM] using this
    have hz : locM w (g⁻¹ * g')⁻¹ = 1 := by
      rw [_root_.mul_inv_rev, inv_inv, locM_mul, hinv, ← locM_mul, inv_mul_cancel, locM_one]
    calc locM w (g⁻¹ * g') = locM w (g⁻¹ * g') * locM w (g⁻¹ * g')⁻¹ := by rw [hz, Matrix.mul_one]
      _ = 1 := by rw [← locM_mul, mul_inv_cancel, locM_one]

end Support

section Conj
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem conj_small {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
    {n : ℕ} {z : GL (Fin n) (AfE F E)} (hz : z ∈ UAd hc n) {P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)}
    (h : Sm Valued.v γ (locM P z⁻¹ - 1)) : Sm Valued.v γ (locM (conjPrime₂ P) z - 1) := by
  classical
  intro i j
  have hcc : conjPrime₂ (conjPrime₂ P) = P := by
    ext b
    rw [mem_conjP, mem_conjP, cO_cO]
  have e := PtExist.inv_apply (inv_mem hz) i j
  rw [inv_inv] at e
  have h1 := h j i
  have e1 : (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j =
      Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F) ((1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
  have key : (locM (conjPrime₂ P) z - 1) i j = adAt F (conjPrime₂ P) (Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F)
      (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) j i - (1 : Matrix (Fin n) (Fin n) (AfE F E)) j i)) := by
    rw [map_sub, ← e, ← e1, map_sub, Matrix.sub_apply]
    simp [locM, Matrix.one_apply]
  have key2 : (locM P z⁻¹ - 1) j i = adAt F P
      (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) j i - (1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) := by
    rw [map_sub, Matrix.sub_apply]
    simp [locM, Matrix.one_apply]
  rw [key, valued_sigR, hcc]
  rw [key2] at h1
  exact h1

end Conj

section Small
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem val_lt_one_le {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem dep_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) :
    dep P d ≤ WithZero.exp (-(d : ℤ)) := by
  unfold dep
  rw [map_pow]
  calc _ ≤ (WithZero.exp (-1 : ℤ)) ^ d := pow_le_pow_left₀ zero_le' (val_lt_one_le val_qOf_lt) d
    _ = WithZero.exp (-(d : ℤ)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp

theorem mem_unitaryAdelic_of_mem_principalCongruence {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
    {n : ℕ} [NeZero n] {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG) :
    z ∈ UAd hc n := by
  obtain ⟨⟨z', hz'⟩, -, rfl⟩ := hz
  exact hz'.1.1

theorem small_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
    {n : ℕ} [NeZero n] {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG)
    {P : HeightOneSpectrum (𝓞 E)} {d : ℕ} (h : Sm Valued.v (dep P d) (locM P z - 1)) :
    (Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM P z - 1) ∧ Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM P z⁻¹ - 1)) ∧
      (Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM (conjPrime₂ P) z - 1) ∧
        Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM (conjPrime₂ P) z⁻¹ - 1)) := by
  have hzU := mem_unitaryAdelic_of_mem_principalCongruence hz
  have hle := dep_le P d
  have hi : Sm Valued.v (dep P d) (locM P z⁻¹ - 1) := by
    have h0 : Sm Valued.v 1 (locM P z⁻¹) := fun i j => valuation_entries_le_one_of_mem_levelGroupOne (inv_mem hz) P i j
    have h1 := h0.mul h
    have e : locM P z⁻¹ * (locM P z - 1) = -(locM P z⁻¹ - 1) := by
      rw [Matrix.mul_sub, ← locM_mul, inv_mul_cancel, locM_one, Matrix.mul_one]
      abel
    rw [e, one_mul] at h1
    intro i j
    have := h1 i j
    rwa [Matrix.neg_apply, Valuation.map_neg] at this
  have h' : Sm Valued.v (dep P d) (locM P z⁻¹⁻¹ - 1) := by rw [inv_inv]; exact h
  refine ⟨⟨fun i j => (h i j).trans hle, fun i j => (hi i j).trans hle⟩, fun i j => (conj_small hzU hi i j).trans hle,
    fun i j => (conj_small (inv_mem hzU) h' i j).trans hle⟩

theorem comm_of_support {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (Q : Finset (HeightOneSpectrum (𝓞 E))) {k z : GL (Fin n) (AfE F E)}
    (hk : ∀ w, w ∈ Q ∨ conjPrime₂ w ∈ Q → locM w k = 1) (hz : ∀ w, w ∉ Q → conjPrime₂ w ∉ Q → locM w z = 1) : z * k = k * z := by
  refine Units.ext (Matrix.ext fun i j => PtExist.ad_ext fun w => ?_)
  show locM w (z * k) i j = locM w (k * z) i j
  rw [locM_mul, locM_mul]
  by_cases h : w ∈ Q ∨ conjPrime₂ w ∈ Q
  · rw [hk w h, Matrix.one_mul, Matrix.mul_one]
  · rw [not_or] at h
    rw [hz w h.1 h.2, Matrix.one_mul, Matrix.mul_one]

end Small

set_option maxHeartbeats 800000 in

theorem approx_zero : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (c : {c // A.chOf 0 c = β}) (x : TC.GA B (B.R.N 0)), x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) → ∃ h : TC.GA B (B.R.N 0), h ∈ (A.K 0 (Nat.zero_le _) β).lev.U ∧ h ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (Formalism.L2.Col.colLev I.Ch 0).grp ∧ ∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0, TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) β).y c).1) * (x * h) * TC.kStd X u (B.R.N 0)) q := by
  intro B X I hI hP l Z u a Ch A hA β hβ c x hx
  obtain ⟨c, rfl⟩ := c
  have hR := hA.reads 0 (Nat.zero_le _)
  have hpt := hR.pt c
  rw [hβ] at hpt
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hks := GlobalTheory.Mem.Col2.MemChart.kStd_spec hPr u (B.R.N 0)
  obtain ⟨p0, hp0, -⟩ := hks.1
  have hTw := (GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away I hI).2 u a
  have hsp := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)
  have hcc : ∀ P : HeightOneSpectrum (𝓞 B.host.E), Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ P) = P := fun P => by
    ext b
    rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]
  have hkT : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w ∈ I.Q a ∨ Formalism.L2.Col.conjPrime₂ w ∈ I.Q a →
      GlobalTheory.Mem.ColAd.locM w (TC.kStd X u (B.R.N 0)) = 1 := by
    intro w hw
    have hT : (B.T u : 𝓞 B.host.F) ∉ (w.under (𝓞 B.host.F)).asIdeal := by
      rcases hw with hw | hw
      · exact (hTw w hw).2.2
      · have e : (Formalism.L2.Col.conjPrime₂ w).under (𝓞 B.host.F) = w.under (𝓞 B.host.F) :=
          (GlobalTheory.Mem.Col2.under_eq_iff B.host w _).2 (Or.inr rfl)
        have := (hTw _ hw).2.2
        rwa [e] at this
    exact GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV w (hks.2.1 _ hT)
  obtain ⟨d, hd⟩ := GlobalTheory.T.stepLevel_contains_unitary_near_one (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev (I.Q a ∪ (I.Q a).image Formalism.L2.Col.conjPrime₂)
  generalize TC.kStd X u (B.R.N 0) = k at hpt hks hp0 hkT ⊢
  have hkU : k ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hp0.1
  have hykU : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * k ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hpt.1
  have hyU : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := by
    have := mul_mem hykU (inv_mem hkU)
    rwa [mul_inv_cancel_right] at this
  have hg : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * k ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := mul_mem (mul_mem hyU hx) hkU
  obtain ⟨z, hz, hsm, hsupp, p, hp⟩ := exists_K1_element_local_support _ _ B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
    (I.Q a) (fun P hP => (hTw P hP).1) ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * k) hg d
  have hzU : z ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := mem_unitaryAdelic_of_mem_principalCongruence hz
  have hcomm : z * k = k * z := comm_of_support (I.Q a) hkT hsupp
  refine ⟨z, hd z ?_ ?_ ?_, Formalism.L2.Col.kOne_le_unipotentLevel _ _ _ _ _ hz, p, ?_⟩
  · rw [hsp.1]
    exact hzU
  · intro w hw
    exact hsupp w (fun h => hw (Finset.mem_union_left _ h))
      (fun h => hw (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, hcc w⟩)))
  · intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact (small_pair hz (hsm ⟨w, hw⟩)).1
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hw
      exact (small_pair hz (hsm ⟨P, hP⟩)).2
  · have e : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * (x * z) * k = (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * k * z :=
      (mul_assoc (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) (x * z) k).trans ((congrArg ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * ·) ((mul_assoc x z k).trans ((congrArg (x * ·) hcomm).trans
        (mul_assoc x k z).symm))).trans ((mul_assoc (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) (x * k) z).symm.trans (congrArg (· * z) (mul_assoc (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) x k).symm)))
    show TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * (x * z) * k) p
    rw [e]
    exact hp

end GlobalTheory.ApproxZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedTranslatesCombinationCommutesSchrodinge
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PlaceModelComb

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem mxAt_of_idemAt {es : AE D} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP) {Q : GlobalTheory.FinPl.Pl D → Prop}
    (hQ : Q (PP.under (𝓞 D.host.F))) {m n : ℕ} {w : Mx D m n} (hw : IsHalf (es + cA D es) w) : GlobalTheory.FinPl.MxAt Q w := by
  obtain ⟨v, ε, hε, hsum⟩ := h.1.2.2
  obtain ⟨q, hqe, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v es ε h.1 hε hsum
  have hv : q.v = PP.under (𝓞 D.host.F) := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under q (hqe ▸ h)
  exact GlobalTheory.LevPin.mxAt_of_half q (hv ▸ hQ) w (hqe ▸ hw)

theorem mxAt_of_idemSum {e : AE D} {Pg : Finset (Pl D.host.E)} (hs : IsIdemSum e Pg) {m n : ℕ} {x : Mx D m n}
    (hx : IsHalf e x ∨ IsHalf (cA D e) x) :
    GlobalTheory.FinPl.MxAt (fun p => ∃ PP ∈ Pg, p = PP.under (𝓞 D.host.F)) x := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hs
  intro i j
  rcases hx with hx | hx
  · rw [← hx i j, Finset.sum_mul]
    refine Ideal.sum_mem _ fun PP hPP => ?_
    have hw : IsHalf (es PP + cA D (es PP)) (es PP • x) := fun a b => by
      obtain ⟨h1, h2, -⟩ := (hes PP hPP).1
      rw [Matrix.smul_apply, smul_eq_mul, add_mul, ← mul_assoc, h1, ← mul_assoc, mul_comm (cA D (es PP)), h2,
        zero_mul, add_zero]
    have := mxAt_of_idemAt (Q := fun p => ∃ PP ∈ Pg, p = PP.under (𝓞 D.host.F)) (hes PP hPP) ⟨PP, hPP, rfl⟩ hw i j
    rwa [Matrix.smul_apply, smul_eq_mul] at this
  · rw [← hx i j, map_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun PP hPP => ?_
    have hw : IsHalf (es PP + cA D (es PP)) (cA D (es PP) • x) := fun a b => by
      obtain ⟨h1, h2, -⟩ := (hes PP hPP).1
      rw [Matrix.smul_apply, smul_eq_mul, add_mul, ← mul_assoc, h2, zero_mul, zero_add, ← mul_assoc, ← map_mul, h1]
    have := mxAt_of_idemAt (Q := fun p => ∃ PP ∈ Pg, p = PP.under (𝓞 D.host.F)) (hes PP hPP) ⟨PP, hPP, rfl⟩ hw i j
    rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (Pg : Finset (Pl D.host.E)) (P' : GlobalTheory.FinPl.Pl D → Prop), IsIdemSum e Pg → (∀ PP ∈ Pg, ¬ P' (PP.under (𝓞 D.host.F))) → ∀ (d : WO S T →₀ ℂ), GlobalTheory.FinPl.CombAt P' d → ∀ (f₁ : WO S T → ℂ) (T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₁ T₁ → (∀ Φ, T₂ Φ = comb ψ S T d (T₁ Φ)) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (comb ψ S T d f₁) T₂ := by
  intro D ψ hψ S T Λ e Pg P' hs hd d hdc f₁ T₁ T₂ hT₁ hT₂
  have hd' : ∀ p, (∃ PP ∈ Pg, p = PP.under (𝓞 D.host.F)) → ¬ P' p := by
    rintro p ⟨PP, hPP, rfl⟩
    exact hd PP hPP
  have hcomm : ∀ x : WO S T, GlobalTheory.FinPl.MxAt (fun p => ∃ PP ∈ Pg, p = PP.under (𝓞 D.host.F)) x → ∀ f,
      heisO ψ S T x (comb ψ S T d f) = comb ψ S T d (heisO ψ S T x f) := by
    intro x hx f
    have h := (GlobalTheory.DisjComb.main D ψ hψ S T _ P' hd').1 (Finsupp.single x 1) d (fun u hu => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
      subst hu
      exact hx) hdc f
    simpa only [GlobalTheory.DisjComb.comb_single] using h
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [hT₂, hT₁.trans Φ hΦ x hx, ← hcomm x (mxAt_of_idemSum hs (Or.inl hx)), hT₂]
  · rw [hT₂, hT₁.modul Φ hΦ y hy, ← hcomm y (mxAt_of_idemSum hs (Or.inr hy)), hT₂]
  · rw [hT₂, hT₁.vac]

end GlobalTheory.PlaceModelComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.NonVanAt

theorem up_eq_setIntegral {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {χA χW : (AE D)ˣ →* Circle}
    {om : GlobalTheory.Core.Rk.IP.WRep A W} (hW : IsWeilDatumO ψ A W χA χW om) {m : Measure (GA D A)} {X : Set (GA D A)}
    (hm : m.IsHaarMeasure) (hX : IsFundamentalDomain (GQ A) X m) {f : WO A W → ℂ} (hf : IsThetaFunO ψ A W f)
    {u : GA D A → ℂ} (hu : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) u) (h : GA D W) :
    GlobalTheory.Core.Rk.IP.up om m f u h = ∫ g in X, thetaKO om g h f * u g ∂m := by
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) (fun g => thetaKO om g h f * u g) := by
    intro γ hγ g
    have e : ((γ * g, h) : GA D A × GA D W) = (γ, 1) * (g, h) := by simp
    have h1 : thetaKO om (γ * g) h f = thetaKO om g h f := by
      unfold thetaKO
      rw [e, map_mul, Module.End.mul_apply]
      exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hf)
    show thetaKO om (γ * g) h f * u (γ * g) = thetaKO om g h f * u g
    rw [h1, hu γ hγ g]
  rw [GlobalTheory.Core.Rk.IP.up, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]

theorem rcoef_zero {D : D7} {A : HSp D} (m : Measure (GA D A)) (b : GA D A) : GlobalTheory.Core.Rk.IP.rcoef m 0 0 b = 0 := by
  simp [GlobalTheory.Core.Rk.IP.rcoef, GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]

set_option maxHeartbeats 1000000 in

theorem nonVan_of_downNe : ∀ (D : D7) (_ : DownNe D) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t := by
  intro D hD G _ _ Pl0 T A Ks _ _ _ R F hG hP i t h hh s hs y hy hy0
  obtain ⟨⟨cA, a, hdef⟩, hpl, hun, hunr, hη, hsig, hrW, hr0, hrV, -, -, -⟩ := GlobalTheory.T.thetaLiftPair_definite_place_character_data D G Pl0 T A Ks R F hG hP i t
  obtain ⟨hlev, hX⟩ := hG.core.models.νV i t
  have hm : (R.νV i t).IsHaarMeasure := hlev.1
  have hW := hG.core.thP.ωP i t
  obtain ⟨l, P, hreal⟩ := GlobalTheory.T.realIntegral_thetaLift_definiteForm_ne_zero D G Pl0 T A Ks R F hG hP i t y hy0 (R.νV i t) hm
  obtain ⟨hA0, hfix⟩ := GlobalTheory.T.linearForm_extV_mem_A0_and_prin_invariant D G Pl0 T A Ks R F hG hP i t cA a hdef y l
  obtain ⟨B, c, hB, hHyp⟩ := GlobalTheory.T.satake_string_gives_simple_pole_hypotheses D G Pl0 T A Ks R F hG hP i t s hs
  obtain ⟨hcart, hfock, hsph, hfixΦ⟩ := GlobalTheory.T.thetaLiftFockVectors_spherical_principalFixed D G Pl0 T A Ks R F hG hP i t P
  have hu0 : (fun g => l (R.extV i t y g)) ≠ 0 := by
    intro h0
    obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
    obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D (Vc D i)
    have : LocallyCompactSpace (GinfC (Vc D i)) := i6.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : BorelSpace (GinfC (Vc D i)) := Subtype.borelSpace _
    refine hreal ν 𝓕 hν Measure.haar inferInstance ?_
    rw [h0]
    simp only [rcoef_zero, mul_zero, integral_zero]
  have hpar := GlobalTheory.T.scalarComponent_parameters_contain_string D G Pl0 T A Ks R F hG hP i t h hh s y hy l hu0 B hB
  have hpar' : GlobalTheory.LFun.IsParamFunV (Vc D i) (under (R.Pg ∪ R.Q t)) (fun g => l (R.extV i t y g)) B :=
    hun.symm ▸ hpar
  have hHyp' : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (under (D := D) (R.Pg ∪ R.Q t) : Set (HeightOneSpectrum (𝓞 D.host.F))) (Wc D i).rank D.R.t c B
      (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
    rw [hrW, hun]; exact hHyp
  have hF : Form R.θ (Vc D i) cA (R.βV i) (R.Pg ∪ R.Q t) (chiV R i t) (Wc D i).rank D.R.t (fun g => l (R.extV i t y g)) B := by
    refine ⟨hA0, hfix, ?_, hunr, c, ?_⟩
    · exact hpar'
    · exact hHyp'
  have hO : Occ R.ψ R.θ (cart (R.MW i (sg0 D A))) (R.ωP i t) (R.νV i t) (R.βV i) (R.Pg ∪ R.Q t)
      (fun g => l (R.extV i t y g)) (R.ptP i t P) := ⟨hcart, hfock, hsph, hfixΦ, hreal⟩
  have hW' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (chiW R i t) (chiV R i t) (R.ωP i t) := hW
  have hr1 : 0 < (Wc D i).rank := by rw [hrW]; exact hr0
  have hr2 : (Vc D i).rank = (Wc D i).rank + D.R.t := by rw [hrW]; exact hrV
  have key := hD R.ψ R.θ (Vc D i) (Wc D i) D.R.t (chiW R i t) (chiV R i t) (R.ωP i t) cA a (R.βV i) (R.Pg ∪ R.Q t)
    (R.νV i t) (fun g => l (R.extV i t y g)) B (cart (R.MW i (sg0 D A))) (R.ptP i t P) hdef hsig hr1 hr2 hη hW' hpl hm hF hO
  by_contra hno
  refine key fun f hf g => ?_
  rw [up_eq_setIntegral hW hm hX hf (GlobalTheory.AutomorphicL2Unitary.leftInv_of_isAutFun (Submodule.mem_inf.1 hA0).1.1.toIsAutFun)]
  by_contra hne
  exact hno ⟨f, l, g, hf, hne⟩

end GlobalTheory.Core.Rk.NonVanAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardMultiplicityCuspidalRealType
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ChainFr

namespace GlobalTheory.Corev.LiftUp

theorem liftUp_mult : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ), S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k → IsWeilExp ψ V W (expS D k) (expT D k) ω → IsVacVec ψ θ M M' f → ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∃ T : PolF D W.rank V.rank → SmT M → SmT M', (∀ P v, T P v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v})) ∧ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = T P v} ∧ LiftsM θ M M' ν 𝓕 (fun P h g => conj (thetaKO ω g h (ptOf ψ θ M M' f P))) T := by
  intro hDS hHC hCD hCW D k V W S S' M M' θ ψ ω f hS hS' hθ hch hω hf ν 𝓕 hν h𝓕
  subst hS hS'
  obtain ⟨X, hX, _h1, _h2, h3, h4, h5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hDS hHC
  have hIn : Inputs D X := GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries hDS hHC hCD hCW D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X hIn (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X hIn (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X hIn (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X hIn)))
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  have hstd : IsStdChar D ψ (-1) := hW.std
  have hadj : AdjLaw ψ V W := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hstd V W
  have h0 : adjO V W 0 = 0 := by
    have := hadj.add 0 0
    simpa using this
  obtain ⟨ω', hW', hω'⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ V W χS χT ω hW
  obtain ⟨j, -, hj⟩ := GlobalTheory.T.fockVectors_conjAdjointPullback_bijection D ψ θ hstd hθ V W (Fr.ofModel M) (Fr.ofModel M')
  obtain ⟨hvac', hpt⟩ := hj f (isVacF_of_isVacVec hf)
  have hω'e : IsWeilExp ψ W V (expT D k) (expS D k) ω' :=
    ⟨χT, χS, hW', fun τ => ⟨(hexp τ).2, (hexp τ).1⟩⟩
  have hne : dag V W f ≠ 0 := by
    intro hz
    apply hf.ne
    funext x
    have hx := congrFun hz (adjO W V x)
    simp only [dag, hadj.invol, Pi.zero_apply] at hx
    simpa using hx
  have hf' : IsVacVec ψ θ M' M (dag V W f) := ⟨hvac'.1, hne, hvac'.2⟩
  obtain ⟨It, hIt⟩ := GlobalTheory.T.exists_realThetaIntertwiner_exchangedPair hDS hHC D k V W _ _ M M' θ ψ rfl rfl hθ hch
  have hItW := hIt ω' (dag V W f) hω'e hf'
  have hrule : ∀ τ, RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) :=
    fun τ => (GlobalTheory.T.firstOccurrenceRule_thetaChainStep_both_directions D X h3 h4 h5 k hch τ).2
  have hL := hPL _ _ _ _ hrule W V M' M θ ψ hθ ω' hω'e (dag V W f) It hf' hItW ν 𝓕 hν h𝓕 (dag V W f)
    (isVacF_of_isVacVec hf')
  refine ⟨fun P v => It (j P) v, fun P v => GlobalTheory.T.real_intertwiner_values_kFinite D W V _ _ M' M θ ψ _ _ ω' (dag V W f) It hθ hω'e hf' hItW (j P) v,
    ?_, ?_⟩
  · refine (GlobalTheory.T.kFiniteSpan_le_span_realIntertwiner_values hDS hHC D W V _ _ M' M θ ψ _ _ ω' (dag V W f) It hθ hω'e hf' hItW).trans
      (Submodule.span_mono ?_)
    rintro w ⟨P, v, hv, rfl⟩
    exact ⟨j.symm P, v, hv, by simp⟩
  · intro F hF
    obtain ⟨F', hF', hF'e⟩ := hL F hF
    refine ⟨F', hF', fun P v h => ?_⟩
    have key : ∀ g, conj (thetaKO ω g h (ptOf ψ θ M M' f P)) =
        thetaKO ω' h g (ptOf ψ θ M' M (dag V W f) (j P)) := by
      intro g
      have e1 : ptOf ψ θ M' M (dag V W f) (j P) = dag V W (ptOf ψ θ M M' f P) := hpt P
      simp only [thetaKO]
      rw [e1, hω']
      simp [dag, h0]
    simp only [key]
    exact hF'e (j P) v h

end GlobalTheory.Corev.LiftUp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleCharacterAtBasePointDetRootRootOfUnityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleCharacter_at_basePointDetRoot_rootOfUnity : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ A.chr (j + 1) (A.xr i β) ^ n = 1 := by
  first | exact @GlobalTheory.CharRoot.chr_xr_pow_eq_one | exact GlobalTheory.CharRoot.chr_xr_pow_eq_one | (intros; apply GlobalTheory.CharRoot.chr_xr_pow_eq_one <;> assumption)
end

