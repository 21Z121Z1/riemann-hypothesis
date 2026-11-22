import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0558
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0525
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSPos
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0561
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0486
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0556
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0562
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryThetaInnerProductFormulaConvergentRange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIdentityAtEveryTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerTup

theorem jetP_cast (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ) (cD : D.what₂.Tau → ℂ)
    (hcD : ∀ τ, cD τ ≠ 0) (G : VCx D.what₂.Tau a b → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    jetP S T hS hT s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) (castP hS hT P)) := by
  subst hS hT
  have h1 : castP (D := D) (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) P = P := by
    conv_rhs => rw [← MvPolynomial.rename_id_apply P]
    rfl
  rw [h1]
  exact GlobalTheory.T.fockPolynomialJetValue_eq_jetLinearForm_rescaled D S T s cD hcD G P

theorem jetC_zero {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) (m : Formalism.L2.Ker.DVar ι a b →₀ ℕ) :
    jetC cD (fun _ : VCx ι a b => (0 : ℂ)) m = 0 := by
  simp only [jetC, derivAt0, iteratedFDeriv_zero_fun, Pi.zero_apply, ContinuousMultilinearMap.zero_apply, mul_zero]

theorem jetP_zero (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : jetP S T hS hT s (fun _ => 0) P = 0 := by
  simp only [jetP, jetC_zero, mul_zero, Finset.sum_const_zero]

theorem jetL_zero {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) : jetL cD (fun _ : VCx ι a b => (0 : ℂ)) = 0 := by
  have h : (fun m => jetC cD (fun _ : VCx ι a b => (0 : ℂ)) m) = 0 := funext fun m => jetC_zero cD m
  simp only [jetL, h, map_zero]

theorem toHom_surj {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (y : (Fin a → D.host.E) →ₗ[D.host.E] Fin b → D.host.E) : ∃ z, toHom S T hS hT z = y :=
  ⟨(Matrix.reindex (finCongr hT) (finCongr hS)).symm (LinearMap.toMatrix' y), by
    unfold toHom
    rw [Equiv.apply_symm_apply, Matrix.toLin'_toMatrix']⟩

theorem supp_per_of_inBox {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a))
    (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (Ξ : Formalism.L2.Col.HomE E a b → K)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox SS cA cB N N' Ξ) (f : K →+* ℂ) (p : ℂ) :
    (∀ y, p * f (Ξ y) ≠ 0 → ((cA * cB : ℕ) : E) • y ∈ Formalism.L2.Col.homAt SS N N') ∧
    (∀ y, ∀ z ∈ Formalism.L2.Col.homAt SS N N', p * f (Ξ (y + ((cA * cB : ℕ) : E) • z)) = p * f (Ξ y)) := by
  have key : ∀ (n : ℕ) (y : Formalism.L2.Col.HomE E a b), ((n : E) • y) = ((n : 𝓞 E) • y) := fun n y => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  refine ⟨fun y hy => ?_, fun y z hz => ?_⟩
  · have hx : Ξ y ≠ 0 := fun h0 => hy (by rw [h0, map_zero, mul_zero])
    have h1 := hB.1 y hx
    rw [Formalism.L2.Col.divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h1
    rw [key, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ h1
  · have hz' : ((cA * cB : ℕ) : E) • z ∈ Formalism.L2.Col.mulLat cB (Formalism.L2.Col.homAt SS N N') := by
      rw [key, Nat.cast_mul, mul_comm, mul_smul]
      exact Submodule.mem_map.2 ⟨_, Submodule.smul_mem _ _ hz, rfl⟩
    rw [hB.2 y _ hz']

theorem jetP_zero' (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : jetP S T hS hT s (0 : VCx D.what₂.Tau a b → ℂ) P = 0 :=
  jetP_zero D S T hS hT s P

theorem jetL_zero' {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) : jetL cD (0 : VCx ι a b → ℂ) = 0 := jetL_zero cD

end GlobalTheory.KerTup

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.KerTup in

theorem GlobalTheory.KerTup.kernel_identity_tuple : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (s : ℂ), (∀ f, IsHol θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) ψ f → ∀ P, pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s (ColDat.xiS θ i hi f) P) → ∀ α γ (c : {c // A.chOf i c = ι i α}) (c' : {c // A.chOf (i + 1) c = ι (i + 1) γ}) P, (volLev (x i).vol (A.U i (ι i α)) : ℂ) * thetaKO (kom i) (A.h i _ c) (A.h (i + 1) _ c') (pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (comb ψ _ _ (dd i α γ) (vac i)) P) = cK i * A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC i hi s hHol α γ c c' P
  obtain ⟨hStd, hGram, hEmb, hcD, hDet⟩ := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  obtain ⟨hFin, Φ, hSB, hΦv, hTh⟩ := hC.dat i hi α γ
  obtain ⟨hMv, hMv', hΞ⟩ := GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB (w i α γ) hΦv c c'
  obtain ⟨xg, hxg⟩ := hDet _ (A.h i (ι i α) c)
  obtain ⟨yh, hyh⟩ := hDet _ (A.h (i + 1) (ι (i + 1) γ) c')
  have hV := (hX.mv i hi).2 a (A.chr (i + 1)) (kom i) (hC.is.chr ⟨i, hi⟩) (hC.om i hi) (A.h i _ c)
    (hC.is.h i (Nat.le_of_succ_le hi) _ c).1 (A.h (i + 1) _ c') (hC.is.h (i + 1) hi _ c').1 _ _ hMv hMv' xg yh hxg hyh
  have hχ := GlobalTheory.T.chainMove_characters_eq_rho_up_to_base I hI hP l Z u a Ch₀ A hC.is i hi _ _ c c' xg yh hxg hyh
  obtain ⟨hc0, hcov, h2qd⟩ := GlobalTheory.T.tupleLevel_pos_odd_badPrimes_prime_to_level I hI hP u a
  obtain ⟨hXo, hPr, -⟩ := base_fields_primes_ok B X
  have hi' : i < B.R.m := hi
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) _ _ u i hXo hPr
    hI.sel_ok (hI.T_mem u) hI.g_mem (hI.idx_ok a) hi' ⟨_, _, _, _, hI.ch_tied⟩ c.1.1 c'.1.1 ((I.stp u a i).rep c.1)
    ((I.stp u a (i + 1)).rep c'.1)
  have hLH := (TC.laHyp_eSmooth_true I hI hP l Z a u i hi').1
  have hLa := (hLH.2.2.2.2.2 _ _ ⟨((I.stp u a i).rep c.1).1.1.deco.2.lat, ((I.stp u a i).rep c.1).1.1.deco.2.uni⟩
    ⟨((I.stp u a (i + 1)).rep c'.1).1.1.deco.2.lat, ((I.stp u a (i + 1)).rep c'.1).1.1.deco.2.uni⟩).2
  have he : B.fields.embC I.A.σ₀ = tauE (I.rec7 l Z) := funext hEmb
  rw [he, ColIn.A_AA] at hLa
  set N := ((I.stp u a i).rep c.1).1.1.deco.1.N with hN
  set N' := ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N with hN'
  have hΞ' : ∀ z, Φ (actO _ _ (A.h i _ c)⁻¹ (A.h (i + 1) _ c')⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) =
      w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1)
        ((I.stp u a (i + 1)).rep c'.1) (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) :=
    fun z => hΞ z
  obtain ⟨hsupp, hper⟩ := supp_per_of_inBox _ _ _ _ _ _ hbox B.embLL (w i α γ)
  have hth : I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) =
      thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
        (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1
          ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.A.e _ _ N N') := by
    rw [← he]
    have h2 : ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) = I.A.AA := (ColIn.A_AA I).symm
    rw [h2]
    rfl
  have hcore := fun (κ : ℂ) (E : VCx (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ) => GlobalTheory.T.thetaKernel_splitPlaces_eq_jet_classicalTheta (I.rec7 l Z) ψ θ _ _ (B.R.N i) (B.R.N (i + 1)) (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))
    (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc (hStd i hi) s hHol (A.chr (i + 1)) (kom i) (hC.om i hi) A.e (ColIn.Sb I a u)
    hC.is.idem (vac i) Φ (comb ψ _ _ (dd i α γ) (vac i)) (hX.vc i hi) hSB hTh (A.h i _ c) (hC.is.h i (Nat.le_of_succ_le hi) _ c).1
    (A.h (i + 1) _ c') (hC.is.h (i + 1) hi _ c').1 N N' hMv hMv' (levC I.sel (I.tup a) (I.cst a) u) hc0 hcov h2qd hLa
    (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) hΞ' hsupp hper κ E
  have hjet := fun G => jetP_cast (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
    I.J.cD hcD G P
  have hxi0 : (∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0) →
      ∀ y : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)), B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y) = 0 := by
    intro hz y
    obtain ⟨z, rfl⟩ := toHom_surj _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) y
    have h0 := (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB 0
      (fun z' => by simp only [hΦv z', hz z', mul_zero]) c c').2.2 z
    have h1 := (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB 1
      (fun z' => by simp only [hΦv z', hz z', mul_zero]) c c').2.2 z
    rw [h0, zero_mul, one_mul] at h1
    exact h1.symm
  by_cases hm : w i α γ ≠ 0 ∧ ∃ z, A.xi i hi (ι i α) (ι (i + 1) γ) z ≠ 0
  · obtain ⟨hw, hxz⟩ := hm
    have hVE : xiN θ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc
        (kom i (A.h i _ c, A.h (i + 1) _ c') (vac i)) = fun z => (c₀ i * (A.chr (i + 1) (A.xr i (ι i α)) : ℂ) *
          (A.chr (i + 1) (A.xr (i + 1) (ι (i + 1) γ)) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * w i α γ) *
          ((w i α γ)⁻¹ * I.A.e _ _ N N' z) := by
      refine hV.trans (funext fun z => ?_)
      have h3 : I.A.e _ _ N N' z = I.A.chiF _ _ N N' * I.J.V.thMoved _ _ N N' z := rfl
      rw [h3, mul_assoc (c₀ i), hχ]
      field_simp
    have hwE : (fun z => w i α γ * ((w i α γ)⁻¹ * I.A.e _ _ N N' z)) = I.A.e _ _ N N' :=
      funext fun z => by rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
    have hT : jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
        (thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
          (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (fun z => (w i α γ)⁻¹ * I.A.e _ _ N N' z)) P =
        jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
      have h6 : thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (fun z => (w i α γ)⁻¹ * I.A.e _ _ N N' z) =
          I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) :=
        (GlobalTheory.T.classicalThetaOfDatum_smul_move _ _ _ _ _ _ _ _ _ _ _ _).trans ((congrArg (fun G => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) G) hwE).trans hth.symm)
      exact (congrArg (fun t => jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s t P) h6).trans (hjet _)
    rw [hcore _ _ hVE, hC.cst i hi α γ hxz]
    refine (congrArg (fun t => _ * (_ * t)) hT).trans ?_
    have hT'' : jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) = A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := mul_comm _ _
    refine Eq.trans ?_ (congrArg (fun t => _ * t) hT'')
    ring
  · have hΞz : (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) = fun _ => 0 := by
      funext y
      by_cases hw : w i α γ = 0
      · rw [hw, zero_mul]
      · have hz : ∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0 := fun z => by_contra fun h => hm ⟨hw, z, h⟩
        rw [hxi0 hz y, mul_zero]
    have hT0 : jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
        (thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
          (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.J.V.thMoved _ _ N N')) P = 0 := by
      have h5 : thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.J.V.thMoved _ _ N N') = 0 :=
        (congrArg (fun G : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → ℂ => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) G (I.J.V.thMoved _ _ N N')) hΞz).trans (thC_zero _ _ _ _ _ _ _ _ _ _)
      exact (congrArg (fun t => jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s t P) h5).trans (jetP_zero' _ _ _ _ _ s P)
    rw [hcore _ _ hV]
    refine (congrArg (fun t => _ * (_ * t)) hT0).trans ?_
    simp only [mul_zero]
    by_cases hxz : ∃ z, A.xi i hi (ι i α) (ι (i + 1) γ) z ≠ 0
    · have hw : w i α γ = 0 := by
        by_contra hw
        exact hm ⟨hw, hxz⟩
      rw [hC.cst i hi α γ hxz, hw]
      simp
    · have hz : ∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0 := fun z => by_contra fun h => hxz ⟨z, h⟩
      have hth0 : I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) = 0 := by
        rw [hth]
        have h4 : (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) = fun _ => 0 := funext (hxi0 hz)
        exact (congrArg (fun G : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → ℂ => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) G (I.A.e _ _ N N')) h4).trans (thC_zero _ _ _ _ _ _ _ _ _ _)
      have hL0 : A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) = 0 := by
        show ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) • jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) = 0
        rw [hth0, jetL_zero', LinearMap.zero_apply, smul_zero]
      exact ((congrArg (fun t => cK i * t) hL0).trans (mul_zero _)).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueDOfTruePack
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.MiTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
open GlobalTheory.MiTop

namespace GlobalTheory.Fam

theorem trueD_of_truePack : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), TruePack W → GlobalTheory.Core.Rk.TrueD D := by
  intro D L hT Gi Gl Kc Yd cX ex W h
  cases h with
  | mk W hA =>
    obtain ⟨hpk, htr, -, -, -, -⟩ := hA
    obtain ⟨hok, ⟨pins⟩, -, ⟨std⟩, -, -⟩ := htr
    refine ⟨_, _, _, _, _, rfl, ⟨⟨hok, pins, W.R.T.cols, std, ?_⟩⟩⟩
    exact
      { toSTies := W.S.toSTies
        hF := hpk.bot.fin
        tr := W.S.tr
        into := W.S.into
        bij := W.S.bij
        lev := W.S.lev
        colPin := W.S.colPin hpk.bot.fin
        inst := W.S.inst
        locTied := W.S.locTied
        pin := hpk.bot.idE }

end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace

theorem levU_iff_inLevG : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ((y : GL _ _) ∈ (F0 W u).cls0.lev.U ↔ GlobalTheory.FamTrace.InLevG a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy
  constructor
  · intro h
    exact ⟨GlobalTheory.T.true_geometry_lattice_forward W hA u a ha hat row col hc κ hκ y hy h, GlobalTheory.T.true_geometry_lattice_image W hA u a ha hat row col hc κ hκ y hy h, GlobalTheory.T.true_geometry_lattice_kernel W hA u a ha hat row col hc κ hκ y hy h⟩
  · intro h
    refine ((F0 W u).cls0.lev.U_eq _).2 ⟨y.2, fun v => ?_⟩
    by_cases hv : (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal)
    · exact GlobalTheory.T.true_geometry_lattice_index W hA u a ha hat row col hc κ hκ y hy h v hv
    · by_cases hb : v ∈ Formalism.L2.Forms.badG (I.rec7 l Z)
      · exact GlobalTheory.T.true_geometry_lattice_measure W hA u a ha hat row col hc κ hκ y hy h v hb
      · exact GlobalTheory.T.true_geometry_lattice_volume W hA u a ha hat row col hc κ hκ y hy h v hb hv

end GlobalTheory.FamTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_tuple_free_value : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ α : J.Ch j, ∃ c : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k, (∀ i, c i ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ GlobalTheory.PenLev.relax J j hj α ∧ ∀ i, c i * GlobalTheory.PenBridge.rd J j hj g i * (c i)⁻¹ ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i))) := by
  first | exact @GlobalTheory.PenLoc.level_iff_relax | exact GlobalTheory.PenLoc.level_iff_relax | (intros; apply GlobalTheory.PenLoc.level_iff_relax <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldOverFlagUnipotentThetaLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem mt_mem_GQ_rat {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = rat M := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩

set_option maxHeartbeats 1000000 in

theorem unfold_over_N_lift : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ n in vN.𝓝, Th n.1 * liftS om vW.μ vW.𝓕 G Φ n.1 ∂vN.ν = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  intro D hD ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hx hTh G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨act, y₀, hy₀, hrel, htrans, hstab1, hstab2⟩ := GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer D V V₀ W ρ d x₀ hx
  letI := act
  obtain ⟨𝓐, h𝓐, hlay⟩ := GlobalTheory.T.flagUnipotent_fundamentalDomain_layers_integral D V V₀ ρ d vN vb vU
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  haveI hΓc : Countable ((NFlagQ V d.e).prod (GQ W)) := Function.Injective.countable
    (f := fun γ : (NFlagQ V d.e).prod (GQ W) => ((⟨γ.1.1, (Subgroup.mem_prod.1 γ.2).1⟩ : NFlagQ V d.e),
      (⟨γ.1.2, (Subgroup.mem_prod.1 γ.2).2⟩ : GQ W)))
    fun a b h => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  haveI : Countable ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)) :=
    (Subgroup.inclusion_injective (Subgroup.map_subtype_le (MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀))).countable
  have hF : IsFundamentalDomain ((NFlagQ V d.e).prod (GQ W)) (vN.𝓝 ×ˢ vW.𝓕) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ vN.𝓝 vW.𝓕 ?_ ?_
    · have hc : ((NFlagQ V d.e).prod (GQ W)).comap (MonoidHom.inl (flagN d) (GA D W)) = NFlagQ V d.e := by
        ext n
        simp only [Subgroup.mem_comap, MonoidHom.inl_apply, Subgroup.mem_prod, one_mem, and_true]
      rw [hc]; exact hN2
    · have hc : ((NFlagQ V d.e).prod (GQ W)).map (MonoidHom.snd (flagN d) (GA D W)) = GQ W := by
        ext h
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact (Subgroup.mem_prod.1 hp).2
        · intro hh
          exact ⟨(1, h), Subgroup.mem_prod.2 ⟨one_mem _, hh⟩, rfl⟩
      rw [hc]; exact vW.fund
  have hG' : IsFundamentalDomain ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _))
      (𝓐 ×ˢ 𝓑) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ 𝓐 𝓑 ?_ ?_
    · rw [hstab1]; exact h𝓐
    · rw [hstab2]; exact h𝓑
  have hmeas : ∀ y : Orb W x₀, Measurable fun p : flagN d × GA D W =>
      Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1 := by
    intro y
    have t4 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS Φ hΦ).2.2.2.1 y.1
    refine Continuous.measurable ?_
    refine ((hTh.cont.comp continuous_fst).mul (hG.2.1.comp continuous_snd)).mul ?_
    exact t4.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hinv : ∀ (γ : (NFlagQ V d.e).prod (GQ W)) (y : Orb W x₀) (p : flagN d × GA D W),
      Th ((γ : flagN d × GA D W) * p).1.1 * G ((γ : flagN d × GA D W) * p).2 *
        term ψ d W vS (om (((γ : flagN d × GA D W) * p).1.1, ((γ : flagN d × GA D W) * p).2) Φ) (γ • y).1 =
      Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1 := by
    intro γ y p
    have hmem := Subgroup.mem_prod.1 γ.2
    have hq1 : ((γ.1.1 : flagN d) : GA D V) ∈ GQ V := hmem.1
    have hq2 : γ.1.2 ∈ GQ W := hmem.2
    obtain ⟨M, hM⟩ := mt_mem_GQ_rat W hq2
    have hΨ := hω.om_pres (p.1.1, p.2) Φ hΦ
    have hΨ' := hω.om_pres (1, γ.1.2) _ hΨ
    have key : term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1, γ.1.2 * p.2) Φ) (γ • y).1 =
        term ψ d W vS (om (p.1.1, p.2) Φ) y.1 := by
      have hsplit : ((γ.1.1 : GA D V) * p.1.1, γ.1.2 * p.2) =
          (((γ.1.1 : GA D V), 1) * ((1 : GA D V), γ.1.2)) * (p.1.1, p.2) := by
        ext <;> simp
      rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have t2 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ').2.1
      have t3 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ).2.2.1
      have e1 : (rat (M * y.1) : Mx D W.rank ρ) = rat (γ • y).1 ⬝ blockX d (γ.1.1 : GA D V) := by
        rw [hrel γ y, hM, rat_mul]
      rw [t2 _ hq1 γ.1.1.2 (γ • y).1 (M * y.1) e1, t3 _ hq2 (M * y.1) y.1 (by rw [hM, rat_mul])]
    have hT : Th ((γ.1.1 : GA D V) * p.1.1) = Th p.1.1 := hTh.left _ hq1 γ.1.1.2 _ p.1.2
    have hGG : G (γ.1.2 * p.2) = G p.2 := hG.1 _ hq2 p.2
    show Th ((γ.1.1 : GA D V) * p.1.1) * G (γ.1.2 * p.2) *
        term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1, γ.1.2 * p.2) Φ) (γ • y).1 = _
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) hT hGG) key
  obtain ⟨hl, hi⟩ := GlobalTheory.T.lintegral_unfold_sum_transitive_orbit (flagN d × GA D W) (vN.ν.prod vW.μ) ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀) y₀ htrans
    (vN.𝓝 ×ˢ vW.𝓕) (𝓐 ×ˢ 𝓑) hF hG'
    (fun y p => Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1) hmeas hinv
  obtain ⟨hfin, hLA⟩ := GlobalTheory.T.unipotentMean_thetaLift_eq_orbitIntegral D hD ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ Th hx hTh G Φ hG hΦ
  simp only [hy₀] at hl hi
  have hfin' := hl ▸ hfin
  obtain ⟨hint, hLC⟩ := GlobalTheory.T.integral_baseTerm_unfolding_coordinates D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hTh G Φ hG hΦ 𝓐 𝓑
    h𝓐.nullMeasurableSet h𝓑.nullMeasurableSet hlay hfin'
  exact ⟨hint, by rw [hLA, ← hi hfin, hLC]⟩

end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryThetaInnerProductFormulaConvergentRangeStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_theta_innerProduct_formula_convergent_range : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : GlobalTheory.Core.Rk.IP.WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧ Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m ∧ petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
  first | exact @GlobalTheory.Core.Rk.IP.innerProduct_convergent | exact GlobalTheory.Core.Rk.IP.innerProduct_convergent | (intros; apply GlobalTheory.Core.Rk.IP.innerProduct_convergent <;> assumption)
end

