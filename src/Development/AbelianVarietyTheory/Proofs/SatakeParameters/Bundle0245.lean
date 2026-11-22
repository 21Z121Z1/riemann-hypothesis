import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0234
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0225
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqNormV
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

theorem v_map_eq_one {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {x : v.adicCompletion K}
    (hx : Valued.v x = 1) : Valued.v (i x) = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h0 : Valued.v (i x) ≠ 0 := by simpa using hx0
  have h1 : Valued.v (i x) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi x).2 hx.le
  have h2 : Valued.v (i x⁻¹) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 (by rw [map_inv₀, hx, inv_one])
  rw [map_inv₀, map_inv₀] at h2
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (i x) * (Valued.v (i x))⁻¹ := (mul_inv_cancel₀ h0).symm
    _ ≤ Valued.v (i x) * 1 := mul_le_mul' le_rfl h2
    _ = Valued.v (i x) := mul_one _

theorem v_map_unif {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {p : v.adicCompletion K}
    (hp : Valued.v p = WithZero.exp (-1)) : Valued.v (i p) = WithZero.exp (-1) := by
  have hp0 : p ≠ 0 := by rintro rfl; rw [map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hlt : Valued.v (i p) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi p).2 (by
    rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have key : ∀ z : w.adicCompletion M, Valued.v z < 1 → Valued.v z ≤ Valued.v (i p) := fun z hz => by
    have hy : Valued.v (i.symm z) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi _).1 (by simpa using hz)
    rw [GlobalTheory.SplitUnif.lt_one_iff, ← hp] at hy
    have h3 : Valued.v (i.symm z / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le
    have h4 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 h3
    rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply] at h4
    have hip : 0 < Valued.v (i p) := by
      rw [zero_lt_iff]; simpa using hp0
    exact (div_le_one₀ hip).1 h4
  obtain ⟨q, hq⟩ := w.valuation_exists_uniformizer M
  have hq' : Valued.v ((q : M) : w.adicCompletion M) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hq]
  refine le_antisymm ((GlobalTheory.SplitUnif.lt_one_iff _).1 hlt) ?_
  rw [← hq']
  exact key _ (by rw [hq', ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)

theorem v_map_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) (x : v.adicCompletion K) :
    Valued.v (i x) = Valued.v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨p0, hp0⟩ := v.valuation_exists_uniformizer K
  set p : v.adicCompletion K := (p0 : v.adicCompletion K)
  have hp : Valued.v p = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hp0]
  have hpne : p ≠ 0 := by rintro h; rw [h, map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hvx : Valued.v x ≠ 0 := by simpa using hx
  set k := WithZero.log (Valued.v x)
  have hk : Valued.v x = WithZero.exp k := (WithZero.exp_log hvx).symm
  obtain ⟨u, hu, e⟩ : ∃ u, Valued.v u = 1 ∧ x = u * (p ^ k)⁻¹ := by
    refine ⟨x * p ^ k, ?_, ?_⟩
    · rw [map_mul, map_zpow₀, hp, hk, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
      simp
    · field_simp
  rw [e]
  simp only [map_mul, map_inv₀, map_zpow₀]
  rw [v_map_eq_one i hi hu, hu, v_map_unif i hi hp, hp]

theorem card_residue (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  have hF : ∀ s : 𝓞 K, Valued.v (algebraMap K (v.adicCompletion K) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap K (v.adicCompletion K)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]

theorem absNorm_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := by
  let ψ : v.adicCompletionIntegers K ≃+* w.adicCompletionIntegers M :=
    { toFun := fun a => ⟨i a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        ((v_map_eq i hi a).le.trans ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2))⟩
      invFun := fun b => ⟨i.symm b, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by
        rw [← v_map_eq i hi, RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (i.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (i.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul i (a : v.adicCompletion K) (b : v.adicCompletion K))
      map_add' := fun a b => Subtype.ext (map_add i (a : v.adicCompletion K) (b : v.adicCompletion K)) }
  rw [← card_residue v, ← card_residue w]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv ψ).toEquiv

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

theorem absNorm_eq_normV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm v.asIdeal = normV v := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

end GlobalTheory.LiftAbsPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensionalStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ), IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → φ' ∈ M := by
  first | exact @GlobalTheory.ConjSpan.conj_span_finite | exact GlobalTheory.ConjSpan.conj_span_finite | (intros; apply GlobalTheory.ConjSpan.conj_span_finite; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebraStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveLattice_sigmaTwo_algebraic_of_invariants_algebraic : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic := by
  first | exact @GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg | exact GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg | (intros; apply GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobalStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_period_of_local_global : ∀ D : D7, SumRepresentations.AdmA D → LGC D → RbEx D → EigPd D := by
  first | exact @GlobalTheory.TameEig.eigPd_holds | exact GlobalTheory.TameEig.eigPd_holds | (intros; apply GlobalTheory.TameEig.eigPd_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryLiftOperatorIsLabelOperatorWithPartner
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDictionary

set_option maxHeartbeats 4000000

variable {D : D7} {G : Type} [Group G] [Fintype G] {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Zero

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem hk_zero (V : HSp D) (P : Pl D.host.E) : hk V P 0 = 0 := Finsupp.sum_zero_index

theorem postOn_zero (V : HSp D) {S} (M : DSModel V S) (T : MMap M) : postOn M 0 T = 0 := by
  ext v
  simp [postOn]

theorem hkF_zero (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (F : Bridge.Gf V → W) : hkF V P 0 F = 0 := by
  funext g
  exact Finsupp.sum_zero_index

theorem ops_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (y : (R.HV j t).H) : h P 0 y = 0 := by
  refine (hM.HV j t).1 ?_
  rw [hh P hP 0 y, map_zero]
  exact hkF_zero _ _ _

theorem match_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) : MatchW R j t P 0 0 := by
  intro y y' hy
  have h0 : y' = 0 := by
    refine (hM.HV j t).1 ?_
    rw [hy, map_zero]
    exact hkF_zero _ _ _
  have e1 : (R.thG j t) y' = 0 := by rw [h0]; exact (R.thG j t).map_zero
  have e2 : (R.HW j (sg0 D A)).e ((R.thG j t) y') = 0 := by rw [e1]; exact (R.HW j (sg0 D A)).e.map_zero
  refine e2.trans ?_
  rw [hk_zero]
  exact (postOn_zero _ _ _).symm

theorem op_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (o : Module.End D.what₂.LL (A.MtCSD j t).Forms) (ho : o = 0)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (x : (A.MtCSD j t).Forms) :
    R.jV j t (o x) = h P 0 (R.jV j t x) := by
  rw [ops_zero R hM j t P hP h hh, ho, LinearMap.zero_apply]
  exact (R.jV j t).map_zero

end Zero

section Cases

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem split_good (F : Face D A) (core : Core R F) (t : T) (P : A.ok t) : Good R t (R.pl P) :=
  ((GlobalTheory.GoodPrimes.good_primes R F core.lev).2.2.2 core.fam t P P.2).1

theorem split_low (F : Face D A) (core : Core R F) (hS : SchurAll R) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  obtain ⟨z, hz, -⟩ := GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime R F core hS j t P
  exact ⟨R.pl P, Finsupp.single (splitLab (Vc D j).rank k) 1, splitC (Wc D j).rank (z k), split_good R F core t P,
    fun h hh x => (GlobalTheory.SplitHeckeLabel.split_ops R F core.lev core.fam core.models).2 j t h hh P k hk x, hz k hk⟩

theorem split_high (F : Face D A) (core : Core R F) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : ¬ k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  have h0 : A.heckeL j t (P, k) = 0 := (core.fam.degL j t P).2 k (not_le.1 hk)
  have hg := split_good R F core t P
  refine ⟨R.pl P, 0, 0, hg, fun h hh x => ?_, match_zero R core.models j t _⟩
  exact op_zero R core.models j t (R.pl P) hg (A.heckeL j t (P, k)) h0 h hh x

end Cases

section Inert

variable {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem inert_valid (hH : HoweUnram) (hI : GlobalTheory.Chain.LiftInteg D) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt)
    (hS : SchurAll R.toRealDat) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (hs : Formalism.L2.Col.InertTypeOk (Vc D j).rank s) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨hg, hconj⟩ := hGoodI t Q Q.2
  have two := GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hI core hS t (R.plI Q) hg hconj (GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hC t _ hg hconj)
  obtain ⟨cW, hW⟩ := (two.2 j).1 (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1)
  refine ⟨R.plI Q, Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1, cW, hg, fun h hh x => ?_, hW⟩
  have hty : ∀ i : A3.okI t × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2 →
      Good R.toRealDat t (R.plI i.1) ∧ conjPl (R.plI i.1) = R.plI i.1 ∧
        (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    intro i hi
    obtain ⟨g1, g2⟩ := hGoodI t i.1 i.1.2
    exact ⟨g1, g2, ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank _).2 ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩
  exact (GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 core.lev core.fam core.models j t (A3.okI t × List ℕ) (fun i => R.plI i.1)
    (fun i => GlobalTheory.Hk3.labIn (Vc D j).rank i.2) (A3.heckeLI j t) (fun i => Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2) hty
    (hC.inert.hL j t).some (Q, s) hs).2.2.2 h hh x

theorem inert_vanish (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (h0 : A3.heckeLI j t (Q, s) = 0) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨hg, -⟩ := hGoodI t Q Q.2
  refine ⟨R.plI Q, 0, 0, hg, fun h hh x => ?_, match_zero R.toRealDat core.models j t _⟩
  exact op_zero R.toRealDat core.models j t (R.plI Q) hg (A3.heckeLI j t (Q, s)) h0 h hh x

end Inert

theorem every_op_label : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ j t, ∃ pl cV cW, LiftDict R j t pl cV cW := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hI hC hEx hS hJ j t
  have core := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC).1 hEx
  have key : ∀ i : (A3.liftI j t).OpIx, ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t ((A3.liftI j t).opAll i x) = h pl cV (R.jV j t x)) ∧
      MatchW R.toRealDat j t pl cV cW := by
    rintro (⟨P, k⟩ | ⟨Q, s⟩)
    · by_cases hk : k ≤ (Vc D j).rank
      · exact split_low R.toRealDat F.lv2 core hS j t P k hk
      · exact split_high R.toRealDat F.lv2 core j t P k hk
    · rcases hJ.L j t Q s with h0 | ⟨s', hs', he⟩
      · exact inert_vanish R F hC hEx j t Q s h0
      · have hrank : A3.A.r + A3.A.t = (Vc D j).rank := (R.B.rankL j).symm
        rw [hrank] at hs'
        obtain ⟨pl, cV, cW, g, o, m⟩ := inert_valid R F hH hI hC hEx hS j t Q s' hs'
        refine ⟨pl, cV, cW, g, fun h hh x => ?_, m⟩
        have e : (A3.liftI j t).opAll (Sum.inr (Q, s)) = A3.heckeLI j t (Q, s') := he
        rw [e]
        exact o h hh x
  choose pl cV cW h1 h2 h3 using key
  exact ⟨pl, cV, cW, ⟨h1, fun h hh i x => h2 i h hh x, h3⟩⟩

end GlobalTheory.LiftDictionary

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryRowOperatorIsLabelOperatorWithPartner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowDictR

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hk_zero (V : HSp D) (P : Pl D.host.E) : hk V P 0 = 0 := by
  unfold hk; exact Finsupp.sum_zero_index

theorem hkF_zero (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (F : Bridge.Gf V → W) :
    hkF V P 0 F = 0 := by
  funext h; unfold hkF; exact Finsupp.sum_zero_index

theorem postOn_hk_zero {V : HSp D} {S : _} (M : DSModel V S) (P : Pl D.host.E) (z : MMap M) : postOn M (hk V P 0) z = 0 := by
  rw [hk_zero]
  rfl

set_option maxHeartbeats 1000000 in

theorem entry_zero (R : RealDat3 D A3 Ks) (hM : R.toRealDat.IsModels) (t : T) (i : (A3.rowI t).OpIx) (p : Pl D.host.E)
    (hp : Good R.toRealDat t p) (h0 : ∀ x, (A3.rowI t).opAll i x = 0) :
    ∃ cX c0 : List ℤ →₀ ℂ, (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll i x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
  refine ⟨0, 0, fun h hh x => ?_, fun y y' hy => ?_⟩
  · have hx : (A3.rowI t).opAll i x = 0 := h0 x
    refine (congrArg (R.jX t) hx).trans ((R.jX t).map_zero.trans ?_)
    refine ((hM.HX t).1 ?_).symm
    refine (hh p hp 0 (R.jX t x)).trans ?_
    rw [hkF_zero, LinearMap.map_zero]
  · have hy0 : y' = 0 := (hM.HX t).1 (by rw [hy, LinearMap.map_zero, hkF_zero])
    subst hy0
    have e1 : R.HE.e (R.Th t 0) = 0 := by simp
    exact e1.trans (postOn_hk_zero _ _ _).symm

set_option maxHeartbeats 1000000 in

theorem entry_split (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hL : GlobalTheory.Chain.LiftInteg D) (hW : R.WeakCharacterisation F)
    (hE : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (t : T) (P0 : A3.A.ok t) (k : ℕ) :
    ∃ (p : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ), Good R.toRealDat t p ∧
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll (Sum.inl (P0, k)) x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hg : Good R.toRealDat t (R.pl P0.1) :=
    ((GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hcore.lev).2.2.2 hcore.fam t P0.1 P0.2).1
  by_cases hk : k ≤ D.sp.X'.rank
  · have hz := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hL hcore hS t P0
    have hop := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models).1 t
    have hm : MatchE R.toRealDat t (R.pl P0.1) (Finsupp.single (splitLab D.sp.X'.rank k) 1)
        (splitC (Yc D 0).rank (hz.choose k)) := hz.choose_spec.1 k hk
    refine ⟨R.pl P0.1, Finsupp.single (splitLab D.sp.X'.rank k) 1, splitC (Yc D 0).rank (hz.choose k), hg,
      fun h hh x => ?_, hm⟩
    have ex : (A3.rowI t).opAll (Sum.inl (P0, k)) x = A3.A.heckeR t (P0, k) x := rfl
    exact (congrArg (R.jX t) ex).trans (hop h hh P0 k hk x)
  · have hd := (hcore.fam.degR t P0).2 k (not_le.1 hk)
    have h0 : ∀ x, (A3.rowI t).opAll (Sum.inl (P0, k)) x = 0 := fun x =>
      (LinearMap.congr_fun hd x).trans (LinearMap.zero_apply x)
    have hz := entry_zero R hcore.models t (Sum.inl (P0, k)) (R.pl P0.1) hg h0
    exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩

set_option maxHeartbeats 1000000 in

theorem entry_valid (hH : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hL : GlobalTheory.Chain.LiftInteg D) (hW : R.WeakCharacterisation F)
    (hE : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (t : T) (Q : A3.okI t) (s s' : List ℕ)
    (hs' : Formalism.L2.Col.InertTypeOk D.sp.X'.rank s') (he : A3.heckeRI t (Q, s) = A3.heckeRI t (Q, s')) :
    ∃ (cX c0 : List ℤ →₀ ℂ),
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll (Sum.inr (Q, s)) x) = h (R.plI Q.1) cX (R.jX t x)) ∧
      MatchE R.toRealDat t (R.plI Q.1) cX c0 := by
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hQ := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1
  have hg := (hQ t Q.1 Q.2).1
  have hc := (hQ t Q.1 Q.2).2
  have hTwo := GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hL hcore hS t _ hg hc (GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hW t _ hg hc)
  have hpre : ∀ j : A3.okI t × List ℕ, Formalism.L2.Col.InertTypeOk D.sp.X'.rank j.2 →
      Good R.toRealDat t (R.plI j.1.1) ∧ conjPl (R.plI j.1.1) = R.plI j.1.1 ∧
        (GlobalTheory.Hk3.labIn D.sp.X'.rank j.2).Pairwise (fun a b => b ≤ a) := fun j hj =>
    ⟨(hQ t j.1.1 j.1.2).1, (hQ t j.1.1 j.1.2).2, ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents D.sp.X'.rank (GlobalTheory.Hk3.labIn D.sp.X'.rank j.2)).2
      ⟨j.2, hj.2.2, hj.1, hj.2.1, rfl⟩).2.1⟩
  have hR := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models t (A3.okI t × List ℕ)
    (fun j => R.plI j.1.1) (fun j => GlobalTheory.Hk3.labIn D.sp.X'.rank j.2) (A3.heckeRI t)
    (fun j => Formalism.L2.Col.InertTypeOk D.sp.X'.rank j.2) hpre (hW.inert.hR t).some (Q, s') hs'
  have hop := hR.2.2.2
  have hc0 := hTwo.1.1 (Finsupp.single (GlobalTheory.Hk3.labIn D.sp.X'.rank s') 1)
  refine ⟨_, hc0.choose, fun h hh x => ?_, hc0.choose_spec⟩
  have ex : (A3.rowI t).opAll (Sum.inr (Q, s)) x = A3.heckeRI t (Q, s') x := LinearMap.congr_fun he x
  exact (congrArg (R.jX t) ex).trans (hop h hh x)

set_option maxHeartbeats 4000000 in

theorem entry_inert (hH : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hL : GlobalTheory.Chain.LiftInteg D) (hW : R.WeakCharacterisation F)
    (hE : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (hJ : InertJunk A3) (t : T) (Q : A3.okI t) (s : List ℕ) :
    ∃ (p : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ), Good R.toRealDat t p ∧
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll (Sum.inr (Q, s)) x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hg := ((GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1 t Q.1 Q.2).1
  by_cases hv : Formalism.L2.Col.InertTypeOk D.sp.X'.rank s
  · have hz := entry_valid hH R F hL hW hE hS t Q s s hv rfl
    exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩
  · have hj := hJ.R t Q s
    rcases hj with h0 | hs
    · have h0' : ∀ x, (A3.rowI t).opAll (Sum.inr (Q, s)) x = 0 := fun x =>
        (LinearMap.congr_fun h0 x).trans (LinearMap.zero_apply x)
      have hz := entry_zero R hcore.models t (Sum.inr (Q, s)) (R.plI Q.1) hg h0'
      exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩
    · have hok : Formalism.L2.Col.InertTypeOk D.sp.X'.rank hs.choose := by
        rw [R.B.rankR]; exact hs.choose_spec.1
      have hz := entry_valid hH R F hL hW hE hS t Q s hs.choose hok hs.choose_spec.2
      exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩

set_option maxHeartbeats 4000000 in

theorem rowDict_exists : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ t, ∃ pl cX c0, RowDict R t pl cX c0 := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hL hW hE hS hJ t
  have key : ∀ i : (A3.rowI t).OpIx, ∃ (p : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ), Good R.toRealDat t p ∧
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll i x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
    rintro (⟨P, k⟩ | ⟨Q, s⟩)
    · exact entry_split R F hL hW hE hS t P k
    · exact entry_inert hH R F hL hW hE hS hJ t Q s
  choose pl cX c0 hg hop hm using key
  exact ⟨pl, cX, c0, ⟨hg, fun h hh i x => hop i h hh x, hm⟩⟩

end GlobalTheory.RowDictR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicGLInductionOverPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicGL_induction_over_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ), 0 < N → ∀ p : GAf L n → Prop, (∀ κ, NG.Cong L n N κ → p κ) → (∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y)) → ∀ g, p g := by
  first | exact @GlobalTheory.PlaceInd.induction_places | exact GlobalTheory.PlaceInd.induction_places | (intros; apply GlobalTheory.PlaceInd.induction_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineParameter_twist_potentiallySemistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw c → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) → GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) = (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpChar (GlobalTheory.Pst.wdAt P ι Bw h hj c) := by
  first | exact @GlobalTheory.TwistParamAbove.wdAt_twist | exact GlobalTheory.TwistParamAbove.wdAt_twist | (intros; apply GlobalTheory.TwistParamAbove.wdAt_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProductStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_split_exact_twistCount_product : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsSmoothChar χ → IsCuspSupport π.π d (fun a => (σ a).π) → Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} = t → ∃ (π₁ : Irr k r) (π₂ : Irr k t), Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) ∧ ∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α) := by
  first | exact @GlobalTheory.BlockSplitProd.main | exact GlobalTheory.BlockSplitProd.main | (intros; apply GlobalTheory.BlockSplitProd.main <;> assumption)
end

