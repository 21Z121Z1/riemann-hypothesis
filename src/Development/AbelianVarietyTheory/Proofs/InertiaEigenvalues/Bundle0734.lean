import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLOfEPowSmulMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterDefiniteUnitaryInertPlace
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatumFnLevPeriod
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

set_option maxHeartbeats 1600000

namespace GlobalTheory.LevPeriod

end GlobalTheory.LevPeriod

namespace GlobalTheory.LevPeriod

theorem exists_split {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (l : Geo.Tor.Level H) :
    ∃ α ∈ l.Mb, ∃ β ∈ Mfr l, α + β = 1 := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by
    rw [Mfr, l.coprime]; exact Submodule.mem_top
  exact Submodule.mem_sup.1 h1

end GlobalTheory.LevPeriod

namespace GlobalTheory.LevPeriod

end GlobalTheory.LevPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DegreeOnePrimeCMFieldOverSplitMaxRealSubfield
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.SplitDegOne

theorem exists_unique_other {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℕ) (a : ι)
    (hpos : ∀ i, 1 ≤ g i) (hsum : ∑ i, g i = 2) (ha : g a = 1) :
    ∃ b, b ≠ a ∧ g b = 1 ∧ ∀ c, c = a ∨ c = b := by
  have h1 : ∑ i ∈ Finset.univ.erase a, g i = 1 := by
    have := Finset.add_sum_erase Finset.univ g (Finset.mem_univ a)
    omega
  have hcard : (Finset.univ.erase a).card ≤ 1 := by
    have := Finset.card_nsmul_le_sum (Finset.univ.erase a) g 1 (fun i _ => hpos i)
    rw [smul_eq_mul, mul_one] at this
    exact this.trans h1.le
  have hne : (Finset.univ.erase a).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at h1
    omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 (le_antisymm hcard hne.card_pos)
  have hbm : b ∈ Finset.univ.erase a := hb ▸ Finset.mem_singleton_self b
  refine ⟨b, Finset.ne_of_mem_erase hbm, by rw [hb, Finset.sum_singleton] at h1; exact h1, fun c => ?_⟩
  by_cases hc : c = a
  · exact Or.inl hc
  · right
    have : c ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩
    rw [hb] at this
    exact Finset.mem_singleton.1 this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) ∧
    (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))).card = 2 ∧
    ∀ w' ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E))),
      Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal ∧
        w'.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
  intro E _ _ _ w hf he
  classical
  let v := w.under (𝓞 (maximalRealSubfield E))
  have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hv0 : v.asIdeal ≠ ⊥ := v.ne_bot
  have hfw : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal w.asIdeal
    rw [hf] at this
    exact (mul_eq_one.1 this.symm).2
  have hew : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal w.asIdeal
    rw [he] at this
    exact (mul_eq_one.1 this.symm).2
  have h2 : Module.finrank (𝓞 (maximalRealSubfield E)) (𝓞 E) = 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
    exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E))
      (maximalRealSubfield E) (𝓞 E) E).symm
  let _ : Fintype (v.asIdeal.primesOver (𝓞 E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [h2] at hsum
  let a : v.asIdeal.primesOver (𝓞 E) := ⟨w.asIdeal, w.isPrime, hwv⟩
  obtain ⟨b, hba, hb1, hall⟩ := exists_unique_other (fun q : v.asIdeal.primesOver (𝓞 E) =>
      q.1.ramificationIdx (𝓞 (maximalRealSubfield E)) * q.1.inertiaDeg (𝓞 (maximalRealSubfield E))) a
    (fun q => by
      have : q.1.IsPrime := q.2.1
      exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 _).ne'
        (Ideal.inertiaDeg_pos q.1 _).ne'))
    hsum (by simp only [a, hew, hfw, mul_one])
  have hbl : b.1.LiesOver v.asIdeal := b.2.2
  let B : HeightOneSpectrum (𝓞 E) := ⟨b.1, b.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 b.1⟩
  have hB : B.under (𝓞 (maximalRealSubfield E)) = v :=
    HeightOneSpectrum.ext (Ideal.over_def b.1 v.asIdeal).symm
  have hwB : w ≠ B := fun h => hba (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h).symm)

  have hmem : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = v → u = w ∨ u = B := by
    intro u hu
    have hul : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu]; rfl⟩
    rcases hall ⟨u.asIdeal, u.isPrime, hul⟩ with h | h
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val h))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val h))
  have hB1 := mul_eq_one.1 hb1
  have hnorm : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = v →
      Ideal.absNorm u.asIdeal = Ideal.absNorm v.asIdeal ∧ u.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    intro u hu
    have hul : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu]; rfl⟩
    have hf1 : u.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield E)) = 1 ∧
        u.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
      rcases hmem u hu with rfl | rfl
      · exact ⟨hfw, hew⟩
      · exact ⟨hB1.2, hB1.1⟩
    refine ⟨?_, hf1.2⟩
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal u.asIdeal, hf1.1, pow_one]
  refine ⟨GlobalTheory.LFun.isSplit_iff.2 ⟨w, B, hwB, rfl, hB⟩, ?_, fun u hu => ?_⟩
  · rw [Finset.card_eq_two]
    refine ⟨w, B, hwB, Finset.ext fun u => ?_⟩
    rw [GlobalTheory.LFun.mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hmem u, by rintro (rfl | rfl); exacts [rfl, hB]⟩
  · have hu' := GlobalTheory.LFun.mem_aboveF.1 hu
    exact ⟨(hnorm u hu').1.trans (hnorm w rfl).1.symm, (hnorm u hu').2⟩

end GlobalTheory.SplitDegOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvKEqSum
section
open scoped TensorProduct

namespace GlobalTheory.EvaluationSum

open GlobalTheory.SeriesTie

theorem evK_eq_sum {D : Formalism.BasicNotions.D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Γ Pl0 I0 (List Nat) T (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D))]
    {Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks}
    {cG : MulEquiv (Formalism.L2.DIV.G0 (Formalism.IndefR.Links.LevCh.Pg (Formalism.IndefR.Links.RealDat.toLevCh (Formalism.IndefR.Links.RealDat3.toRealDat Rl))) (Formalism.BasicNotions.Ranks.r (Formalism.BasicNotions.D7.R D))) (Formalism.BasicNotions.G0g (Formalism.BasicNotions.D7.nd D))}
    {S : Formalism.IndefR.NX.RatDat (Formalism.BasicNotions.D7.ntw D)} (YS : Formalism.IndefR.NX.NExpRealS Rl cG S)
    (v₀ : (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) → (σ : RingHom (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Complex) → Formalism.IndefR.Mult.DSModel.Vec (Formalism.IndefR.Links.RealDat.MW (Formalism.IndefR.Links.RealDat3.toRealDat Rl) j σ))
    {ρ : GlobalTheory.SeriesTie.Setup (Formalism.BasicNotions.D7.ntw D)} (hρ : GlobalTheory.SeriesTie.Setup.Good ρ)
    (i : Formalism.BasicNotions.NTw.Tw (Formalism.BasicNotions.D7.ntw D)) (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) (b : Bool)
    (t : TensorProduct (Formalism.IndefR.NX.RatDat.Ks S) (Formalism.IndefR.NX.KB S i b) (Formalism.IndefR.NX.FmK S ((j : ℕ) + 1))) :
    ∃ (n : ℕ) (a : Fin n → Formalism.IndefR.NX.KB S i b) (x : Fin n → Formalism.IndefR.NX.FmK S ((j : ℕ) + 1)),
      GlobalTheory.SeriesTie.evK YS v₀ hρ i j b t =
        ∑ k : Fin n, GlobalTheory.SeriesTie.Setup.e ρ i b (a k) • GlobalTheory.SeriesTie.evW YS v₀ j (x k).val := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a f => exact ⟨1, fun _ => a, fun _ => f, by simp [evK_tmul]⟩
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨n₁, a₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, a₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ + n₂, Fin.append a₁ a₂, Fin.append x₁ x₂, ?_⟩
    rw [map_add, e₁, e₂, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.EvaluationSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistablePeriodsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisinFrame_semistablePeriods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Frame bk N d ρ), F.IsDR ∧ ((∀ g, s.κ g = 1) → F.IsCr) := by
  first | (exact @GlobalTheory.semistablePeriodFrame) | (exact GlobalTheory.semistablePeriodFrame) | (intros; apply GlobalTheory.semistablePeriodFrame  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleTameDescentGoodLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem exists_pack_isOfType : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), (∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ H) → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∃ Pk : Pack a ϖ η H T, Pk.D.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) := by
  intro hBS hF l _ a e _ _ ϖ LL _ _ hl Pl AI hstd η H Sig U hU T hT
  obtain ⟨F⟩ := GlobalTheory.nonempty_crysBKFunctorOL_of_bhattScholze hBS l a e ϖ LL Pl AI hstd
  let B := F.obj (resF T (ϖ.field a)) hT.crys
  let I : Ident (thetaW a LL) ϖ B.P T := Ident.ofRes B.I
  have hBK : IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) :=
    B.isBK
  obtain ⟨C, hC, hTay⟩ := GlobalTheory.T.integralConnection_taylorFormula_tameBreuilKisin hBS l a e ϖ LL hl (Fin B.n) B.P T I hBK
  obtain ⟨⟨jB, hcmp⟩, -⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (Fin B.n) B.P T I
  have hhor := GlobalTheory.T.galois_fixes_crystalline_image_descentDatum l a e ϖ LL hl (Fin B.n) B.P T I jB hcmp C hC hTay
  obtain ⟨hst, hinf⟩ := GlobalTheory.T.breuilKisin_tensorAinf_galoisStable_kummerFixed l a e ϖ LL (Fin B.n) B.P T I hBK
  have hK7 := GlobalTheory.T.kummerTowerGalois_preserves_breuilKisinModule hBS l a e ϖ LL (Fin B.n) B.P T I hBK
  obtain ⟨⟨Δ, hΔ⟩, hLA⟩ := GlobalTheory.T.exists_galoisDescentDatum_and_stable l a e ϖ LL (Fin B.n) B.P T I hinf hK7
  obtain ⟨hEN, hjU⟩ := GlobalTheory.T.breuilKisin_lattice_stable_and_hodgeTate_jumps hF l a e ϖ LL hl (Fin B.n) B.P T I jB Pl AI hstd hcmp hhor
  have hj : B.P.jumps ⊆ (U : Set ℤ) := hjU _ hT.jumps
  have hIcc : B.P.jumps ⊆ Set.Icc (-(η : ℤ)) H := fun i hi => hU i (hj hi)
  obtain ⟨hlow, hup⟩ := (GlobalTheory.BK.PhiMod.jumps_subset_Icc_iff _ _ l e a (Fin B.n) B.P η H).1 hIcc
  have hch := GlobalTheory.T.tameInertiaCharacters_subset_tameType l a e ϖ LL hl (Fin B.n) B.P T I jB Δ Pl AI hstd hcmp hhor hΔ Sig hT.type
  let D : BKDat ↥(OL LL) ↥LL.1 l e a (Fin B.n) η H :=
    { toPhiMod := B.P
      desc := Δ
      nabla_mem := fun m hm => hC ▸ C.mem_MM m hm
      EN_mem := hEN
      lower := hlow
      upper := hup }
  let R : GalDat (thetaW a LL) ϖ (sQ l) D T :=
    { I := I
      jB := jB
      cmp := hcmp
      desc := hΔ
      stable := hLA hst
      horiz := hhor }
  exact ⟨⟨B.n, D, R, hBK⟩, ⟨hch, hj⟩⟩

end GlobalTheory.BKGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenFamily
section
namespace GlobalTheory.EigenFamilyStabilizer

def stab {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (θ : G → ℂ)
    (h1 : θ 1 = 1) (hm : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (y : ι → V) : Subgroup K where
  carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
  one_mem' := ⟨by simpa using h1, fun i => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun i => ?_⟩
    · rw [Subgroup.coe_mul, hm _ a.2 _ b.2, ha, hb, one_mul]
    · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun i => ?_⟩
    · have := hm _ (a⁻¹).2 _ a.2
      rw [ha, mul_one, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, h1] at this
      exact this.symm
    · conv_lhs => rw [← ha' i]
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      simp

theorem exists_eigen_family : ∀ {G V W ι : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V] [inst_4 : Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : Module ℂ W] [inst_7 : Fintype ι] {ρ : Representation ℂ G V}, GlobalTheory.PRep.IsSmooth ρ → ∀ {K : Subgroup G}, IsCompact (↑K : Set G) → ∀ {U : Set G}, IsOpen U → (1 : G) ∈ U → ∀ (θ : G → ℂ), (∀ g ∈ U, g ∈ K → θ g = (1 : ℂ)) → (∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) → ∀ (T : ι → V →ₗ[ℂ] W) (y : ι → V), (∀ k ∈ K, ∑ i : ι, (T i : V → W) (((ρ : G → V →ₗ[ℂ] V) k : V → V) (y i)) = θ k • ∑ i : ι, (T i : V → W) (y i)) → ∃ (u : ι → V), (∀ (j : ι), ∀ h ∈ K, ((ρ : G → V →ₗ[ℂ] V) h : V → V) (u j) = θ h • u j) ∧ ∑ i : ι, (T i : V → W) (u i) = ∑ i : ι, (T i : V → W) (y i) := by
  intro G V W ι _ _ _ _ _ _ _ _ ρ hρ K hK U hU hU1 θ hθ hm T y hy
  classical
  have h1 : θ 1 = 1 := hθ 1 hU1 K.one_mem
  let H : Subgroup K := stab ρ K θ h1 hm y
  have hHo : IsOpen (H : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds H (g := 1)
    have ho : IsOpen (U ∩ ⋂ i, {g : G | ρ g (y i) = y i}) :=
      hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))
    have ho' : IsOpen ((Subtype.val : K → G) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho'.mem_nhds ?_) ?_
    · refine ⟨hU1, Set.mem_iInter.2 fun i => ?_⟩
      simp
    · rintro k ⟨hk, hk'⟩
      exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : ι → K → V := fun j k => θ (k⁻¹ : K) • ρ k (y j)
  have hf : ∀ j (k : K) (s : K), s ∈ H → f j (k * s) = f j k := by
    intro j k s hs
    have hs' : θ (s⁻¹ : K) = 1 := (H.inv_mem hs).1
    simp only [f]
    rw [mul_inv_rev, Subgroup.coe_mul, hm _ (s⁻¹).2 _ (k⁻¹).2, hs', one_mul, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply, hs.2 j]
  let F : ι → K ⧸ H → V := fun j q => f j q.out
  have hF : ∀ j (k : K), F j (k : K ⧸ H) = f j k := by
    intro j k
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul H k
    simp only [F]
    rw [hs, hf j k s s.2]
  have hact : ∀ j (h : K) (q : K ⧸ H), ρ h (F j q) = θ h • F j (h • q) := by
    intro j h q
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, hF, hF]
      simp only [f]
      rw [map_smul, smul_smul, mul_comm (θ h), ← hm _ ((h * k)⁻¹).2 _ h.2, ← Subgroup.coe_mul,
        Subgroup.coe_mul K h k, map_mul, Module.End.mul_apply]
      congr 3
      group
  have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun j => (Fintype.card (K ⧸ H) : ℂ)⁻¹ • ∑ q, F j q, fun j h hh => ?_, ?_⟩
  · rw [map_smul, map_sum, smul_comm]
    congr 1
    rw [Finset.sum_congr rfl fun q _ => hact j ⟨h, hh⟩ q, ← Finset.smul_sum]
    congr 1
    exact Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (F j)
  · have hq : ∀ q, ∑ i, T i (F i q) = ∑ i, T i (y i) := by
      intro q
      simp only [F, f, map_smul]
      rw [← Finset.smul_sum, hy _ q.out.2, smul_smul, ← hm _ (q.out⁻¹).2 _ q.out.2, ← Subgroup.coe_mul,
        inv_mul_cancel, Subgroup.coe_one, h1, one_smul]
    simp only [map_smul, map_sum]
    rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]

end GlobalTheory.EigenFamilyStabilizer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInverseLocalArtinWeilGroupHomStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_localArtin_weilGroup_hom : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧ (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) ∧ ∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  first | exact @GlobalTheory.InvLocalArtin.exists_invLocalArtin | exact GlobalTheory.InvLocalArtin.exists_invLocalArtin | (intros; apply GlobalTheory.InvLocalArtin.exists_invLocalArtin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHeckeDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeDatumExists

variable {D : D7}

theorem conj_ne_of_split {P : Pl D.host.E} (h : IsSplitPl D.host P) : Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  obtain ⟨x, hx, hy⟩ := h
  refine hy (Formalism.DivisionValues.cO D.host.E x) ?_ ?_
  · show starRingAut (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [starRingAut_apply]
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host _
  · have : Formalism.DivisionValues.cO _ x ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hx
    rwa [hP] at this

theorem exists_isDC_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {α : GA D V}
    (hα : α ∈ GfC V) : ∃ R : Finset (GA D V), Bridge.IsDC (Lev.levG V β L) α R := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hle : Lev.levG V β L ≤ GfC V := fun k hk => hk.1
  have hi := GlobalTheory.HeckeLabels.relIndex_conj_ne_zero (L := GfC V) (GlobalTheory.ParahoricCompact.isCompact_levG V β L)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L) (fun k hk hk' => ⟨hk, hk'⟩) hα
  rw [inf_eq_left.2 hle] at hi
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeLabels.exists_reps hi
  refine ⟨R, fun a ha => ?_, fun g ⟨k₁, k₂, hg⟩ => ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, e⟩ := r1 a ha
    exact ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, e⟩
  · exact r2 g ⟨k₁, k₁.2, k₂, k₂.2, hg⟩

theorem exists_isHeckeDatum : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X),
    ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool), ∀ (k : ℕ) (P : Pl D.host.E), Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P →
      ∃ α R z, ρ.IsHeckeDatum i j b k P α R z := by
  intro D N X ρ _ i j b k P hk
  obtain ⟨-, hkr, hsp, -⟩ := hk
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conj_ne_of_split hsp)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  obtain ⟨α, R₀, R₀', hα, -⟩ := GlobalTheory.Hk3.SplitMatch.exists_data he h1 h2 (Wc D j)
  have hA := (hα k (hkr.trans (r_le_rank_Wc j))).1
  obtain ⟨R, hR⟩ := exists_isDC_levG (Wc D j) _ _ hA.1
  have hee : e * e = e := he.1.1
  set u : (AE D)ˣ := Matrix.GeneralLinearGroup.det (matHom (Wc D j) (α k)) with hu
  have huv : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := Units.mul_inv u
  let z : (AE D)ˣ := Units.mkOfMulEqOne (e * u + (1 - e)) (e * ((u⁻¹ : (AE D)ˣ) : AE D) + (1 - e)) (by
    linear_combination ((u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) - u - ((u⁻¹ : (AE D)ˣ) : AE D) + 1) * hee + e * huv)
  refine ⟨α k, R, z, ⟨e, ϖ, he, h1, h2, hA⟩, hR, ?_⟩
  show (z : AE D) = idemAt P * (mt (Wc D j) (α k)).det + (1 - idemAt P)
  rw [idemAt_eq he]
  rfl

end GlobalTheory.HeckeDatumExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalTranslatesSpanPrescribedCoefficientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localTranslatesSpan_prescribedCoefficient : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : WO S T → ℂ, IsSBHalf a (latH S T ΛS ΛT) Φ → ∀ x₁, IsHalf a x₁ → ∃ f' ∈ locSpan ψ S T a f, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f') = Φ x * ℓ (heisO ψ S T x₁ f) := by
  first | exact @GlobalTheory.DownLift.SplitCoef.exists_locSpan_coef_eq | exact GlobalTheory.DownLift.SplitCoef.exists_locSpan_coef_eq | (intros; apply GlobalTheory.DownLift.SplitCoef.exists_locSpan_coef_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIsUnitary
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.UnitaryTwist

def normRpow (r : ℝ) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 z.ne_zero) r).ne')
  map_one' := by ext; simp
  map_mul' z w := by
    ext
    simp [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

theorem normRpow_val (r : ℝ) (z : ℂˣ) : ((normRpow r z : ℂˣ) : ℂ) = ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ) := rfl

theorem continuous_normRpow (r : ℝ) : Continuous (normRpow r) := by
  have hn : Continuous fun z : ℂˣ => ‖(z : ℂ)‖ := Units.continuous_val.norm
  have hp : Continuous fun z : ℂˣ => ‖(z : ℂ)‖ ^ r :=
    hn.rpow_const fun z => Or.inl (norm_pos_iff.2 z.ne_zero).ne'
  have hc : Continuous fun z : ℂˣ => ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ) := Complex.continuous_ofReal.comp hp
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  have : (fun z : ℂˣ => (((normRpow r z)⁻¹ : ℂˣ) : ℂ)) = fun z : ℂˣ => (((‖(z : ℂ)‖ ^ r : ℝ) : ℂ))⁻¹ := by
    funext z; rw [Units.val_inv_eq_inv_val, normRpow_val]
  rw [this]
  exact hc.inv₀ fun z => Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 z.ne_zero) r).ne'

def normTwist {E : Type} [Field E] [NumberField E] (ω : HChar E) (r : ℝ) : HChar E :=
  ⟨(normRpow r).comp ω.1, (continuous_normRpow r).comp ω.2.1, fun k => by
    rw [MonoidHom.comp_apply, ω.2.2 k, map_one]⟩

theorem exists_pow_mul_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (ω : HChar E) (a : ℕ),
    1 ≤ a → ∃ ν : HChar E, (ω * ν ^ a).IsUnitary := by
  intro E _ _ _ ω a ha
  refine ⟨normTwist ω (-(1 / (a : ℝ))), fun x => ?_⟩
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 ha)
  have ht : 0 < ‖((ω.1 x : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (ω.1 x).ne_zero
  set t : ℝ := ‖((ω.1 x : ℂˣ) : ℂ)‖ with htdef
  have hv : (((normTwist ω (-(1 / (a : ℝ)))).1 x : ℂˣ) : ℂ) = ((t ^ (-(1 / (a : ℝ))) : ℝ) : ℂ) := rfl
  have hm : (((ω * normTwist ω (-(1 / (a : ℝ))) ^ a).1 x : ℂˣ) : ℂ) =
      ((ω.1 x : ℂˣ) : ℂ) * (((normTwist ω (-(1 / (a : ℝ)))).1 x : ℂˣ) : ℂ) ^ a := by
    rw [Subgroup.coe_mul, Subgroup.coe_pow, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val]
  show ‖(((ω * normTwist ω (-(1 / (a : ℝ))) ^ a).1 x : ℂˣ) : ℂ)‖ = 1
  rw [hm, hv, norm_mul, norm_pow, ← htdef, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _), ← Real.rpow_natCast,
    ← Real.rpow_mul ht.le, show -(1 / (a : ℝ)) * (a : ℝ) = -1 by field_simp, Real.rpow_neg_one,
    mul_inv_cancel₀ ht.ne']

end GlobalTheory.UnitaryTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterDefiniteUnitaryInertPlaceStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_definiteUnitary_inertPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → Formalism.UG.IsUnramInv ϖ s q → (∀ L : Subgroup (finU E n), IsOpen (L : Set (finU E n)) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C})) → (∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧ (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧ ∀ x g, cLoc w x = 1 → x * ι g = ι g * x) → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → IsUnramU π w → ∃ α, HasSatAt π w s ϖ q α := by
  first | exact @GlobalTheory.UnitaryBC.SatEx.exists_hasSatAt | exact GlobalTheory.UnitaryBC.SatEx.exists_hasSatAt | (intros; apply GlobalTheory.UnitaryBC.SatEx.exists_hasSatAt <;> assumption)
end

