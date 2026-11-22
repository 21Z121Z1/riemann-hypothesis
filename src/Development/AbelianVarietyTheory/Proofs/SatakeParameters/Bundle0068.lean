import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0062
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordHypothesesEveryLatticeSurjection
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem exists_primitiveRoot_of_good {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (hG : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.2 hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hmem : ζ ∈ Ks K 1 := by
    refine (le_sup_right : _ ≤ Ks K 1) (IntermediateField.subset_adjoin _ _ ?_)
    simpa using hζ.pow_eq_one
  have hLL : ζ ∈ LL.1 := hG.2.2.2 (Ks K 1).val ⟨ζ, hmem⟩
  refine ⟨⟨ζ, hLL⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ LL.1.val.toRingHom.injective

theorem setCS_of_wordsAT {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l}
    (hG : Good K 1 LL) (Wc : Wach P K LL) (hs : Wc.s = 1) (hK : K.1 ≤ MaximalUnramifiedExtension l) (h11 : 11 ≤ l)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] (Wd : NWord (Module.finrank ℚ_[l] ↥(K0 K))) (d : ℕ)
    (hA : WordsAT l Wd d) (T₁ T₂ : Lat K LL) (F : LatHom T₁.L T₂.L) (hF : F.Onto)
    (c₁ : IsCrys (P.PD K) T₁.ρ) (c₂ : IsCrys (P.PD K) T₂.ρ)
    (hj : ∀ a, TruncatedSeriesCountingBounds.JumpsAt Wc T₁ a (Wd.win a))
    (hlow : ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), TruncatedSeriesCountingBounds.lowCount Wc T₂ a Wd.η ≤ (Wd.m : ℤ)) :
    RamifiedCoefficientChains.SetCS Wc d T₁ T₂ F Wd.sz Wd.S Wd.η Wd.m := by
  classical
  obtain ⟨hev, hup, -, -, hbig⟩ := hA
  have hp : (P.PD K).p = l := P.PD_p K
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  obtain ⟨a₀, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (ZMod (Module.finrank ℚ_[l] ↥(K0 K))))
    Finset.univ_nonempty Wd.sz
  have hgr : IsGreatest (Set.range Wd.sz) (Finset.univ.sup Wd.sz) := by
    refine ⟨⟨a₀, hsup.symm⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Finset.le_sup (Finset.mem_univ a)
  have hbig' := hbig _ hgr
  refine ⟨⟨?_, hs, by omega⟩, by omega, hev, ?_, by rw [hp]; exact exists_primitiveRoot_of_good hG, ⟨c₁, c₂, hF⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩⟩
  · exact (goodO_finExt_integers l LL).1
  · intro a τ hτ u hu
    have hw := hj a τ hτ u hu
    have hua := hup a
    unfold NWord.win at hw
    unfold RamifiedCoefficientChains.JumpWinS
    by_cases hpar : (a.val + d) % 2 = 1
    · have h0 : ¬ (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = true := by simpa [hpar] using hua
      simp only [hu1, if_true, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_false, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
    · have h0 : (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = false := by simpa [hpar] using hua
      simp only [hu1, Bool.false_eq_true, if_false, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_true, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
  · intro a τ hτ
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    letI ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    have h := hlow ft a
    unfold TruncatedSeriesCountingBounds.lowCount at h
    have hfil : (Finset.univ.filter (fun τ' => Formalism.MainNotions.LiftingTheory.Over Wc τ' a)) = {τ} := by
      ext τ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' => (existsUnique_over P K LL Wc hK a).unique h' hτ, fun h' => h' ▸ hτ⟩
    rw [hfil, Finset.sum_singleton] at h
    exact h
  · intro a
    have h := (hbig' a).2
    rw [hp]
    unfold RamifiedCoefficientChains.aR RamifiedCoefficientChains.lam RamifiedCoefficientChains.hpar
    push_cast
    exact h
  · intro a
    have h := (hbig' a).1
    unfold RamifiedCoefficientChains.hpar
    push_cast
    exact h

theorem settingC_of_wordsAT : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)) (d : ℕ), 11 ≤ D.nd.l i → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → WordsAT (D.nd.l i) Wd d → RecS.AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d := by
  intro D L HW i r ρ π w hw Cx hG Wd d h11 hB hA nz T₁ T₂ F h₁ h₂ hF
  have hT1 := hB.t1 T₁ h₁
  have hT2 := hB.t2 T₂ h₂
  exact setCS_of_wordsAT hG (WW HW i w hw Cx hG) ((HW (D.nd.l i)).W_s _ 1 _ hG) hB.unram h11 Wd d hA
    T₁ T₂ F hF hT1.1 hT2.1 hT1.2.1 hT2.2

end GlobalTheory.HTW.RecS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainDataGuarded
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

noncomputable section

namespace GlobalTheory.LastSteps

def ChainDataGuarded : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ), Pr.Ok → cst.Ok → R.m = m2 + 2 →
    ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs →
      (∀ hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1), SplitAt Ch sel mu cst m2 P hal) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → DualFn P.1 (fhat sel mu cst P f)) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → FnMod P.1 (topDatum Ch sel mu cst m2 P f)) ∧
      (∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (al : L.β m2),
        L.h m2 al P ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1) →
        ∀ (u : Pr.Word) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p₀.deco.1.N p.deco.1.N (facPen Ch sel mu cst L m2 al p₀ p Y P)) ∧
      (∀ (u : Pr.Word), (∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal) →
        ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P))

def LastTwoStepsGuarded : Prop := FourierLattice ∧ ChainDataGuarded

end GlobalTheory.LastSteps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationDualWeightInvolutiveStatement
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ ε : ℤˣ, ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∀ g : MP R (m + 1), CofRel R m ν f g → CofRel R m (nuDual ν) g ((ε : ℤ) • f) := by
  first | exact @GlobalTheory.ValCmp.Invol.cofRel_invol | exact GlobalTheory.ValCmp.Invol.cofRel_invol | (intros; apply GlobalTheory.ValCmp.Invol.cofRel_invol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowActEquivariantStatement
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowAct_equivariant : ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit h.det → ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ g : MP K (m + 1), CofRel K m ν f g → CofRel K m ν (rowAct K h⁻¹ f) (h.det ^ (-(ν 0 : ℤ)) • rowAct K h.transpose g) := by
  first | exact @GlobalTheory.ValCmp.Eqv.cofRel_rowAct | exact GlobalTheory.ValCmp.Eqv.cofRel_rowAct | (intros; apply GlobalTheory.ValCmp.Eqv.cofRel_rowAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwapStatement
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowDiv_swap : ∀ (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ) (f g : MP R (m + 1)), a ≠ b → CofRel R m ν f g → CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  first | exact @GlobalTheory.ValCmp.cofRel_rowDiv | exact GlobalTheory.ValCmp.cofRel_rowDiv | (intros; apply GlobalTheory.ValCmp.cofRel_rowDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCyclotomicCharacterPeriodDatumStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_cyclotomicCharacter_periodDatum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l), Continuous (fun s => ((cycLL (P.PD K) ↥LL.1 s : (↥LL.1)ˣ) : ↥LL.1)) := by
  first | exact @GlobalTheory.HTW.Rec.continuous_cycLL_period | exact GlobalTheory.HTW.Rec.continuous_cycLL_period | (intros; apply GlobalTheory.HTW.Rec.continuous_cycLL_period <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
section
noncomputable section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
open Filter Topology

namespace GlobalTheory.HeckeSplit

variable {L : Type} [Field L] [NumberField L]

theorem eventually_unrAt (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) :
    ∀ᶠ v in Filter.cofinite, UnrAt χ v := by
  have h : ∀ v : HeightOneSpectrum (𝓞 L), ∃ x : (v.adicCompletion L)ˣ,
      Valued.v (x : v.adicCompletion L) = 1 ∧
      (‖((χ (localIdele L v x) : ℂˣ) : ℂ) - 1‖ < 1 / 2 → UnrAt χ v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
    refine (hc _ ?_).1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  choose x hx hx' using h
  have hc : Continuous fun a : Ideles L => ‖((χ a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp hχ).sub continuous_const).norm
  have h0 : Tendsto (fun v => localIdele L v (x v)) cofinite (𝓝 1) :=
    GlobalTheory.Mem.UnrAe.tendsto_localIdele x hx
  have h1 := (hc.tendsto 1).comp h0
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact h2.mono fun v hv => hx' v hv

theorem exists_level (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 L)) :
    ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ,
      Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1 := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (hχ.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele v))).sub
      continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat + 1, fun x hx1 => ?_⟩
  have hlt : Valued.v ((x : v.adicCompletion L) - 1) < 1 := by
    refine hx1.trans_lt ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := by
    have := Valuation.map_one_add_of_lt _ hlt
    simpa using this
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)

def truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) : Ideles L :=
  infIdele L (infPart L x) * ∏ v ∈ T, localIdele L v (finPart L v x)

theorem truncIdele_inv (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    truncIdele x⁻¹ T = (truncIdele x T)⁻¹ := by
  simp only [truncIdele, map_inv, Finset.prod_inv_distrib, ← mul_inv]

open Classical in
theorem finPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (v : HeightOneSpectrum (𝓞 L)) :
    finPart L v (truncIdele x T) = if v ∈ T then finPart L v x else 1 := by
  rw [truncIdele, map_mul, finPart_infIdele, one_mul, map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem v h fun w _ hw => finPart_localIdele_ne L hw.symm _,
      finPart_localIdele]
  · exact Finset.prod_eq_one fun w hw => finPart_localIdele_ne L (v := w) (w := v) (fun e => h (by rw [e]; exact hw)) _

theorem infPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    infPart L (truncIdele x T) = infPart L x := by
  rw [truncIdele, map_mul, infPart_infIdele, map_prod,
    Finset.prod_eq_one fun v _ => infPart_localIdele L v _, mul_one]

theorem coe_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L) =
      ((x : AdeleRing (𝓞 L) L).1, GlobalTheory.HeckeProduct.cut (x : AdeleRing (𝓞 L) L).2 T) := by
  classical
  refine Prod.ext ?_ (Subtype.ext (funext fun v => ?_))
  · exact congrArg (fun u : (InfiniteAdeleRing L)ˣ => (u : InfiniteAdeleRing L)) (infPart_truncIdele x T)
  · have h := congrArg (fun u : (v.adicCompletion L)ˣ => (u : v.adicCompletion L))
      (finPart_truncIdele x T v)
    refine h.trans ?_
    by_cases hv : v ∈ T
    · simp only [hv, if_true]; exact (if_pos hv).symm
    · simp only [hv, if_false]; exact (if_neg hv).symm

theorem tendsto_truncIdele (x : Ideles L) :
    Tendsto (truncIdele x) atTop (𝓝 x) := by
  have h : ∀ x : Ideles L, Tendsto (fun T => ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L))
      atTop (𝓝 (x : AdeleRing (𝓞 L) L)) := fun x => by
    simp only [coe_truncIdele]
    exact tendsto_const_nhds.prodMk_nhds (GlobalTheory.HeckeProduct.tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
  have h2 := h x⁻¹
  simp only [truncIdele_inv] at h2
  exact h2

theorem char_eq_prod_local (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (x : Ideles L)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) :
    χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) := by
  classical
  have h1 := (hχ.tendsto x).comp (tendsto_truncIdele x)
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop S] with T hT
  change _ = χ (truncIdele x T)
  rw [truncIdele, map_mul, map_prod]
  congr 1
  exact Finset.prod_subset hT fun v _ hv => hS v hv

theorem continuous_char_factor : ∀ (L : Type) [Field L] [NumberField L] (χ : Ideles L →* ℂˣ), Continuous χ → (∀ᶠ v in Filter.cofinite, UnrAt χ v) ∧ (∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ, Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1) ∧ ∀ (x : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) → χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) :=
  fun _ _ _ χ hχ => ⟨eventually_unrAt χ hχ, exists_level χ hχ, fun x S hS => char_eq_prod_local χ hχ x S hS⟩

end GlobalTheory.HeckeSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousOfInvariant
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.PadicFourierLattice

open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

variable {g : ℕ} [hg : Fact g.Prime] {n : ℕ}

lemma g_ne : (g : ℚ_[g]) ≠ 0 := by exact_mod_cast hg.out.ne_zero

lemma gR_pos : (0 : ℝ) < g := by exact_mod_cast hg.out.pos

lemma norm_g : ‖(g : ℚ_[g])‖ = (g : ℝ)⁻¹ := Padic.norm_p

lemma norm_le_inv {x : ℚ_[g]} (h : ‖x‖ < 1) : ‖x‖ ≤ (g : ℝ)⁻¹ := by
  have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one x (-1)).2 (by simpa using h)
  simpa using this

lemma norm_div_g_le {x : ℚ_[g]} (h : ‖x‖ < 1) : ‖x / (g : ℚ_[g])‖ ≤ 1 := by
  rw [norm_div, norm_g, div_le_one (inv_pos.2 gR_pos)]
  exact norm_le_inv h

lemma exists_rep (x : ℚ_[g]) (h : ‖(g : ℚ_[g]) * x‖ ≤ 1) :
    ∃ t : Fin g, ‖x - ((t : ℕ) : ℚ_[g]) / (g : ℚ_[g])‖ ≤ 1 := by
  let z : ℤ_[g] := ⟨(g : ℚ_[g]) * x, h⟩
  refine ⟨⟨PadicInt.zmodRepr z, PadicInt.zmodRepr_lt_p z⟩, ?_⟩
  have h1 := PadicInt.sub_zmodRepr_mem z
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h1
  have h2 : ‖(g : ℚ_[g]) * x - ((PadicInt.zmodRepr z : ℕ) : ℚ_[g])‖ < 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h1
    exact h1
  have h3 := norm_div_g_le h2
  rwa [sub_div, mul_div_cancel_left₀ _ g_ne] at h3

end GlobalTheory.PadicFourierLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersLetterwiseStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicWordMarkedClusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t → (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨ ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  first | exact @GlobalTheory.HTW.Rec.clusters_letterwise | exact GlobalTheory.HTW.Rec.clusters_letterwise | (intros; apply GlobalTheory.HTW.Rec.clusters_letterwise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimension
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

namespace GlobalTheory.Pst.DmapNonzero

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

def subRep (ρ : Representation LL ↥(GK K) V) (S : Submodule LL V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) :
    Representation LL ↥(GK K) ↥S where
  toFun g := (ρ g).restrict (hS g)
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by simp)

@[simp] theorem coe_subRep (ρ : Representation LL ↥(GK K) V) (S : Submodule LL V)
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : ↥(GK K)) (v : ↥S) : ((subRep ρ S hS g v : ↥S) : V) = ρ g v := rfl

theorem tensV_eq_rTensor {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.Pst.DmapNonzero

open GlobalTheory.Pst.DmapNonzero in

theorem GlobalTheory.Pst.DmapNonzero.exists_dmap_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL], (∀ (W : Type) [AddCommGroup W] [Module LL W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] LL W] [FiniteDimensional ℚ_[l] W] (ρW : Representation LL ↥(GK K) W), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W) → ∀ {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'} (hf : ∀ g v, f (ρ g v) = ρ' g (f v)), IsPst P ρ → f ≠ 0 → ∃ x : ↥(Dpst P ρ), GlobalTheory.Pst.DpstMap.dmap P hf x ≠ 0 := by
  intro l _ P K LL _ _ _ hb V V' _ _ _ _ _ _ _ _ _ ρ ρ' f hf hV hf0
  classical
  by_contra hcon
  push_neg at hcon
  let S : Submodule LL V := LinearMap.ker f
  have hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S := fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hf, hv, map_zero]
  let ρS := subRep ρ S hS
  have hfS : ∀ g v, S.subtype (ρS g v) = ρ g (S.subtype v) := fun _ _ => rfl
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans LL V
  haveI : FiniteDimensional ℚ_[l] ↥S :=
    Module.Finite.of_injective (S.subtype.restrictScalars ℚ_[l]) S.injective_subtype

  have hex : Function.Exact (S.subtype.restrictScalars ℚ_[l]) (f.restrictScalars ℚ_[l]) := by
    intro v
    constructor
    · intro h; exact ⟨⟨v, h⟩, rfl⟩
    · rintro ⟨w, rfl⟩; exact w.2
  have hexT := Module.Flat.rTensor_exact (Bst P) hex
  have hinj : Function.Injective ((S.subtype.restrictScalars ℚ_[l]).rTensor (Bst P)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ S.injective_subtype
  let j := dmap P hfS
  have hsurj : Function.Surjective j := by
    intro y
    have h0 : tensV P f (y : V ⊗[ℚ_[l]] Bst P) = 0 := congrArg Subtype.val (hcon y)
    rw [tensV_eq_rTensor] at h0
    obtain ⟨z, hz⟩ := (hexT _).mp h0
    have hz' : tensV P S.subtype z = y := by rw [tensV_eq_rTensor]; exact hz
    obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
    have hzD : z ∈ Dpst P ρS := by
      refine (mem_Dpst P ρS).mpr ⟨K', fun g hg => hinj ?_⟩
      rw [← tensV_eq_rTensor, ← tensV_eq_rTensor, tensV_stRep P ρS ρ S.subtype hfS, hz', hK' g hg]
    exact ⟨⟨z, hzD⟩, Subtype.ext hz'⟩
  let jU : DpstUr P ρS →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ :=
    { toFun := fun x => toUr P ρ (j ((toUr P ρS).symm x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun c x => dmap_mulD P hfS c ((toUr P ρS).symm x) }
  have hjU : Function.Surjective jU := fun y => by
    obtain ⟨x, hx⟩ := hsurj ((toUr P ρ).symm y)
    refine ⟨toUr P ρS x, ?_⟩
    show toUr P ρ (j ((toUr P ρS).symm (toUr P ρS x))) = y
    rw [AddEquiv.symm_apply_apply, hx, AddEquiv.apply_symm_apply]
  have h1 := jU.rank_le_of_surjective hjU
  have h2 := hb ↥S ρS
  have h3 : finrank ℚ_[l] ↥S < finrank ℚ_[l] V := by
    have hne : S.restrictScalars ℚ_[l] ≠ ⊤ := by
      rw [Ne, Submodule.restrictScalars_eq_top_iff, LinearMap.ker_eq_top]
      exact hf0
    exact Submodule.finrank_lt hne
  have h4 : Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) = (finrank ℚ_[l] V : Cardinal) := by
    rw [hV, Module.finrank_eq_rank]
  have h5 : ((finrank ℚ_[l] V : ℕ) : Cardinal) ≤ (finrank ℚ_[l] ↥S : ℕ) := h4 ▸ h1.trans h2
  exact absurd (Nat.cast_le.mp h5) (not_le.mpr h3)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScaleStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eleven_le_inertOddPrimeImagQuadratic_large_scale : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ), L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  first | exact @GlobalTheory.InertPrimeEleven.eleven_le | exact GlobalTheory.InertPrimeEleven.eleven_le | (intros; apply GlobalTheory.InertPrimeEleven.eleven_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDecorationExtensionAtPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decoration_extension_at_primes : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet E n ST ∅) (f : SG → (Sp E n ≃ₗ[E] Sp E n)), (∀ (w : SG) (x : Sp E n), f w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) → ∃ d' : DecoSet E n ST SG, d'.1.N = d.1.N ∧ d'.1.f = d.1.f ∧ ∀ w : SG, ∀ x ∈ stdAt E n w.1, d'.1.be w (f w x) = redV w.1 x := by
  first | exact @GlobalTheory.FrameDeco.exists_deco_of_frames | exact GlobalTheory.FrameDeco.exists_deco_of_frames | (intros; apply GlobalTheory.FrameDeco.exists_deco_of_frames <;> assumption)
end

