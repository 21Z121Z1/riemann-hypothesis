import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0870
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0868
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0459
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTrivialCharLevelEltRationalAtTwistPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

open Formalism.L2.DIV Formalism.L2.Col Formalism.UG GlobalTheory.Mem.Col2.AdT GlobalTheory.Mem.Col2.TC

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevelAll

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_one_apply (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (r s : Fin n) :
    adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

theorem conj_bound (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E)) (ε : WithZero (Multiplicative ℤ)) (hε : ε < 1)
    (hP : ∀ r s, Valued.v (adAt F P (u.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ ε) (r s : Fin n) :
    Valued.v (adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s) ≤ ε := by
  subst hJ
  have hinv := GlobalTheory.Mem.Col2.AdT.Opn.inv_eq_cT hc.sig hu
  have h1 : (1 + ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) *
      (1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) = 1 := by
    rw [← hinv, add_sub_cancel, Units.mul_inv]
  have h2 := congrArg (adAt F (conjPrime₂ P)).mapMatrix h1
  rw [map_mul, map_add, map_add, map_one] at h2
  have key := GlobalTheory.Mem.Col2.AdT.Opn.val_inv_le Valued.v _ _ h2 ε hε (fun a b => ?_) r s
  · have e : ((adAt F (conjPrime₂ P)).mapMatrix ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) r s =
        adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s := by
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub, adAt_one_apply]
    rw [← e]; exact key
  · show Valued.v (adAt F (conjPrime₂ P) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) b a))) ≤ ε
    rw [GlobalTheory.Mem.Col2.valued_sigR hc, GlobalTheory.CharValCompare.conjP_conjP, Matrix.sub_apply, map_sub, adAt_one_apply]
    exact hP b a

end Gen

theorem map_prod_cases {G M κ : Type} [Monoid G] [Monoid M] (f : κ → G) (c : G →* M)
    (hpair : ∀ P P' : κ, P ≠ P' → c (f P) = 1 ∨ c (f P') = 1) :
    ∀ L : List κ, L.Nodup → c (L.map f).prod = 1 ∨ ∃ P ∈ L, c (L.map f).prod = c (f P) := by
  have hall : ∀ (P : κ) (L : List κ), c (f P) ≠ 1 → (∀ P' ∈ L, P' ≠ P) → c (L.map f).prod = 1 := by
    intro P L h1 hL
    induction L with
    | nil => simp
    | cons P' L ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih fun x hx => hL x (List.mem_cons_of_mem _ hx), mul_one]
      exact (hpair P P' (Ne.symm (hL P' (List.mem_cons.2 (Or.inl rfl))))).resolve_left h1
  intro L
  induction L with
  | nil => intro _; left; simp
  | cons P L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases h1 : c (f P) = 1
    · rw [h1, one_mul]
      rcases ih hL.2 with h | ⟨P', hP', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨P', List.mem_cons_of_mem _ hP', h⟩
    · rw [hall P L h1 fun P' hP' e => hL.1 (e ▸ hP'), mul_one]
      exact Or.inr ⟨P, List.mem_cons.2 (Or.inl rfl), rfl⟩

set_option maxHeartbeats 12000000 in

theorem exists_level_elt_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z S → ∀ (N : ℕ) (g : TC.GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P (((g * (show TC.GA B (B.R.N i) from z.1) : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin (B.R.N i)), Valued.v (adAt B.host.F P (((show TC.GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s)) ≤ WithZero.exp (-(N : ℤ)) := by
  intro B X I hOk hPins l Z a T i hi bad S hChi N g
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hgr : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : S.U →* GA B (B.R.N i) := S.U.subtype
  have hexp : WithZero.exp (-((max N 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(N : ℤ)) := WithZero.exp_le_exp.2 (by omega)
  have hexp1 : WithZero.exp (-((max N 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hs : ∀ P : SBof I a, GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := fun P => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) 0 P 1).1
  have hsep : ∀ P P' : SBof I a, P ≠ P' → P.1 ∈ I.Q a → (P'.1 = P.1 ∨ P'.1 = Formalism.L2.Col.conjPrime₂ P.1) → False := by
    intro P P' hne hP h
    rcases h with h | h
    · exact hne (Subtype.ext h.symm)
    obtain ⟨v, hv, hv'⟩ := LevelElt.place_under I hOk hPins l Z a P hP
    apply hv' P' (Ne.symm hne)
    rw [hs] at hv ⊢
    have hc := congrArg HeightOneSpectrum.asIdeal ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).2 (Or.inr h))
    exact Eq.trans hv hc.symm
  have hsel : ∀ P : SBof I a, ∃ z : S.U, S.chi z = 1 ∧
      (∀ Q : HeightOneSpectrum (𝓞 B.fields.E), cP Q (ι z) = 1 ∨ (P.1 ∈ I.Q a ∧ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1))) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) r s, Valued.v (cP Q (ι z) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g * (show GA B (B.R.N i) from z.1) : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, -⟩ := LevelElt.place_under I hOk hPins l Z a P hP
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := LevelElt.one_prime I hOk hPins l Z a T i hi bad S hChi P hP v hv (max N 1) g 1
      have hzU := ((S.U_eq _).1 z.2).1
      have hbP := ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) (max N 1) P z.1).2.2).1 hz3
      have hvP := hv
      rw [hs] at hvP
      have hoff : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), ¬ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1) → cP Q (ι z) = 1 := fun Q hQ =>
        Matrix.ext fun r s => by
          rw [cP_apply]
          exact LevelElt.support_one z.1 v hz2 Q (fun hO => hQ ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 Q).1
            (HeightOneSpectrum.ext (Eq.trans (Eq.symm hO) hvP)))) r s
      refine ⟨z, hz1, fun Q => ?_, fun Q r s => ?_, fun _ => ?_⟩
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · exact Or.inr ⟨hP, hQ⟩
        · exact Or.inl (hoff Q hQ)
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · rw [cP_apply]
          rcases hQ with rfl | rfl
          · exact (hbP r s).trans hexp
          · exact (conj_bound (I.rec7 l Z).sp.cm hgr hzU P.1 _ hexp1 hbP r s).trans hexp
        · rw [hoff Q hQ, sub_self, Valuation.map_zero]
          exact zero_le'
      · obtain ⟨γ, hγ⟩ := hz4
        exact ⟨γ, fun r s => by rw [← hγ r s, mul_one]⟩
    · refine ⟨1, map_one _, fun Q => Or.inl (by rw [map_one, map_one]), fun Q r s => ?_, fun h => absurd h hP⟩
      rw [map_one, map_one, sub_self, Valuation.map_zero]; exact zero_le'
  choose zf hzf1 hzf2 hzf3 hzf4 using hsel
  have hpair : ∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) (P P' : SBof I a), P ≠ P' → cP Q (ι (zf P)) = 1 ∨ cP Q (ι (zf P')) = 1 := by
    intro Q P P' hne
    rcases hzf2 P Q with h | ⟨hP, hQ⟩
    · exact Or.inl h
    rcases hzf2 P' Q with h' | ⟨-, hQ'⟩
    · exact Or.inr h'
    exfalso
    apply hsep P P' hne hP
    rcases hQ with rfl | rfl <;> rcases hQ' with h2 | h2
    · exact Or.inl h2.symm
    · refine Or.inr ?_
      rw [h2, GlobalTheory.CharValCompare.conjP_conjP]
    · exact Or.inr h2.symm
    · have h3 := congrArg Formalism.L2.Col.conjPrime₂ h2
      rw [GlobalTheory.CharValCompare.conjP_conjP, GlobalTheory.CharValCompare.conjP_conjP] at h3
      exact Or.inl h3.symm
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := by
    intro P P' hne
    rcases hzf2 P P'.1 with h | ⟨hP, hQ⟩
    · exact h
    · exact (hsep P P' hne.symm hP hQ).elim
  have hlistP : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, map_mul, ih hL.2]
      by_cases h : P = P'
      · subst h
        simp [hL.1]
      · rw [hone P P' (Ne.symm h)]
        simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : S.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlistP _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hchiw : S.chi w = 1 := by
    rw [hw, map_list_prod]
    refine List.prod_eq_one fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [List.mem_map] at hz
    obtain ⟨P, -, rfl⟩ := hz
    exact hzf1 P
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨w, hchiw, fun P hP => ?_, fun Q r s => ?_⟩
  · obtain ⟨γ, hγ⟩ := hzf4 ⟨P, hQsub P hP⟩ hP
    refine ⟨(γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E), fun r s => ?_⟩
    have e0 : cP P (ι w) = cP P (ι (zf ⟨P, hQsub P hP⟩)) := hwP ⟨P, hQsub P hP⟩
    have e1 : cP P (g * ι w) = cP P (g * ι (zf ⟨P, hQsub P hP⟩)) := by rw [map_mul, map_mul, e0]
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · rw [map_sub, adAt_one_apply]
    change Valued.v (cP Q (ι w) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ _
    rcases map_prod_cases zf ((cP Q).comp ι) (hpair Q) _ (Finset.nodup_toList _) with h | ⟨P, -, h⟩
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h, sub_self, Valuation.map_zero]; exact zero_le'
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h]; exact hzf3 P Q r s

end GlobalTheory.Mem.Col2.AdT.LevelAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockMatrixCoefficientSplitsRealFiniteFactors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCoefSplit

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem actO_inf : ∀ (D : D7) (S T : HSp D) (a : GA D S) (b : GA D T), a ∈ GinfC S → b ∈ GinfC T →
    ∀ w : WO S T, w.map (infPart D) = 0 → actO S T a b w = w := by
  intro D S T a b ha hb w hw
  have hfb : (Formalism.L2.Theta.mt T b).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin T.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 hb)
    exact h
  have hfa : (Formalism.L2.Theta.mt S a⁻¹).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 (Subgroup.inv_mem _ ha))
    exact h
  have h0 : ∀ k j, infPart D (w k j) = 0 := fun k j => by
    have := congrFun (congrFun hw k) j
    simpa using this
  have e1 : Formalism.L2.Theta.mt T b * w = w := by
    ext i j
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · rw [Matrix.mul_apply, map_sum]
      simp [h0]
    · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt T b i k) = if i = k then 1 else 0 := fun k => by
        have := congrFun (congrFun hfb i) k
        simpa [Matrix.one_apply] using this
      rw [Matrix.mul_apply, map_sum]
      simp [h1]
  have e2 : w * Formalism.L2.Theta.mt S a⁻¹ = w := by
    ext i j
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · rw [Matrix.mul_apply, map_sum]
      simp [h0]
    · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt S a⁻¹ k j) = if k = j then 1 else 0 := fun k => by
        have := congrFun (congrFun hfa k) j
        simpa [Matrix.one_apply] using this
      rw [Matrix.mul_apply, map_sum]
      simp [h1]
  unfold actO
  rw [e1, e2]

open GlobalTheory.VacPairSchur GlobalTheory.RawLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem om_heisO_inf {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {a : GA D S} (ha : a ∈ GinfC S) {b : GA D T} (hb : b ∈ GinfC T)
    {w : WO S T} (hw : w.map (infPart D) = 0) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (a, b) (heisO ψ S T w f) = heisO ψ S T w (om (a, b) f) := by
  rw [hom.om_heis a b w f hf, actO_inf D S T a b ha hb w hw]

theorem fockVac_om_fin {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) {x : GA D S} (hx : x ∈ GfC S) {y : GA D T} (hy : y ∈ GfC T) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ J f) :
    IsFockVacAt (heisO ψ S T) θ τ J (om (x, y) f) := by
  have e : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      compAt θ τ (Formalism.L2.Theta.mt T y) * z * compAt θ τ (Formalism.L2.Theta.mt S x⁻¹) = z := fun z => by
    rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (Subgroup.inv_mem _ hx),
      Matrix.one_mul, Matrix.mul_one]
  intro z
  have h := congrArg (om (x, y)) (hv z)
  unfold annih at h ⊢
  rw [map_add, map_smul, GlobalTheory.OrientedHeis.om_dRho hom hθ x y τ z hf, GlobalTheory.OrientedHeis.om_dRho hom hθ x y τ (J z) hf,
    e, e, map_zero] at h
  exact h

theorem om_fin_pureTensorO {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {x : GA D S} (hx : x ∈ GfC S) {y : GA D T}
    (hy : y ∈ GfC T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (x, y) (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (x, y) f) P :=
  (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT x y
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hx, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hx, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, Matrix.one_mul]) f hf P).2

theorem l2_eq_star (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    l2 μ 𝓕 f g = star (thetaIP μ 𝓕 f g) := by
  unfold l2 Formalism.IndefR.Lift.pet thetaIP
  change _ = (starRingEnd ℂ) (∫ w in 𝓕, star (f w) * g w ∂μ)
  rw [← integral_conj]
  congr 1
  funext w
  simp [mul_comm]

theorem pair_eq_inf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ P P' : MvPolynomial (FVar D T.rank S.rank) ℂ, ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → thetaIP μ 𝓕 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') = c * thetaIP μ 𝓕 f g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓕 hcv a ha b hb P P'
  have hψ := hom.std
  have hμ := hcv.1
  have h𝓕 := hcv.2.1
  have thp : ∀ f, IsThetaFunO ψ S T f → ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) :=
    fun f hf Q => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ sS BS sT BT hf Q
  have thom : ∀ f, IsThetaFunO ψ S T f → ∀ Q,
      IsThetaFunO ψ S T (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) :=
    fun f hf Q => hom.om_pres _ _ (thp f hf Q)
  have key : ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ Q,
      thetaIP μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f Q) (pureTensorO ψ θ S T sS sT BS BT f Q) =
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp Q Q * (nrm2 μ 𝓕 f : ℂ) := by
    intro f hf vf Q
    rw [thetaIP_eq_ipO]
    exact GlobalTheory.FockIsometry.ipO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (fun τ => min (pS τ) S.rank)
      (fun τ => min (pT τ) T.rank) (fun τ => min_le_right _ _) (fun τ => min_le_right _ _) hcS hcT
      (fun τ => onb_min (hoS τ)) (fun τ => onb_min (hoT τ)) f hf vf μ 𝓕 hcv Q Q
  set Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun f g =>
    thetaIP μ 𝓕 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') with hΦ
  have hl : ∀ (z : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (z • f + f') g = star z * Φ f g + Φ f' g := by
    intro z f f' g hf hf' hg _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT z hf hf' P, map_add, map_smul, thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (thp g hg P') (GlobalTheory.OrientedHeis.theta_smul z (thom f hf P)) (thom f' hf' P),
      GlobalTheory.Size.ipO_smul_right]
    rfl
  have hr : ∀ (z : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (z • g + g') = z * Φ f g + Φ f g' := by
    intro z f g g' hf hg hg' _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT z hg hg' P', thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul z (thp g hg P')) (thp g' hg' P') (thom f hf P),
      GlobalTheory.Size.ipO_smul_left]
  have hbd : ∃ C : ℝ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      ‖Φ f g‖ ^ 2 ≤ C * (nrm2 μ 𝓕 f * nrm2 μ 𝓕 g) := by
    refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P P).re * (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P' P').re, fun f g hf hg vf vg => ?_⟩
    simp only [hΦ]
    have h1 := cs hψ hcv (thom f hf P) (thp g hg P')
    rw [GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓕 hom hcv _ _ _ (thp f hf P) (thp f hf P),
      key f hf vf P, key g hg vg P', Complex.re_mul_ofReal, Complex.re_mul_ofReal] at h1
    linarith
  have hi : ∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g := by
    intro w hw f g hf hg _ _
    simp only [hΦ]
    rw [pT_heisO hθ sS BS sT BT f hw, pT_heisO hθ sS BS sT BT g hw, om_heisO_inf hom ha hb hw (thp f hf P),
      thetaInner_heisenberg hψ hcv (thom f hf P) (thp g hg P')]
  exact GlobalTheory.T.schur_finiteHeisenberg_fockVacuumThetaFunctions D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv Φ hl hr hbd hi

end GlobalTheory.FockCoefSplit

namespace GlobalTheory.FockCoefSplit

open GlobalTheory.RawLift

theorem coef_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ pS pT : D.what₂.Tau → ℕ, (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q)) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ x ∈ GfC S, ∀ y ∈ GfC T, ∀ Q Q', l2 μ 𝓧 (om (x * a, y * b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 f f = l2 μ 𝓧 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 (om (x, y) f) f := by
  intro D ψ θ S T χS χT om hθ hom μ 𝓧 hcv sS BS sT BT hcS hcT pS pT hoS hoT f hf hvf hpt a ha b hb x hx y hy Q Q'
  obtain ⟨c, hc⟩ := pair_eq_inf D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓧 hcv a ha b hb Q Q'
  have hx' : x⁻¹ ∈ GfC S := Subgroup.inv_mem _ hx
  have hy' : y⁻¹ ∈ GfC T := Subgroup.inv_mem _ hy
  have hg : IsThetaFunO ψ S T (om (x⁻¹, y⁻¹) f) := hom.om_pres _ _ hf
  have hvg : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x⁻¹, y⁻¹) f) :=
    fun τ => fockVac_om_fin hom hθ hx' hy' τ _ hf (hvf τ)
  have inv : ∀ A B : WO S T → ℂ, IsThetaFunO ψ S T A → IsThetaFunO ψ S T B →
      thetaIP μ 𝓧 (om (x, y) A) B = thetaIP μ 𝓧 A (om (x⁻¹, y⁻¹) B) := by
    intro A B hA hB
    have e : om (x, y) (om (x⁻¹, y⁻¹) B) = B := by
      rw [← Module.End.mul_apply, ← map_mul,
        show ((x, y) * (x⁻¹, y⁻¹) : GA D S × GA D T) = 1 from mul_inv_cancel (x, y), map_one, Module.End.one_apply]
    calc thetaIP μ 𝓧 (om (x, y) A) B = thetaIP μ 𝓧 (om (x, y) A) (om (x, y) (om (x⁻¹, y⁻¹) B)) := by rw [e]
      _ = thetaIP μ 𝓧 A (om (x⁻¹, y⁻¹) B) :=
        GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓧 hom hcv _ _ _ hA (hom.om_pres _ _ hB)
  have e1 : om (x * a, y * b) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      om (x, y) (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) := by
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  simp only [l2_eq_star]
  rw [← star_mul', ← star_mul']
  congr 1
  rw [e1, inv _ _ (hom.om_pres _ _ (hpt Q)) (hpt Q'), om_fin_pureTensorO hom hθ sS BS sT BT hx' hy' hf Q',
    hc f _ hf hg hvf hvg, inv _ _ hf hf, hc f f hf hf hvf hvf]
  ring

end GlobalTheory.FockCoefSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem idV_props : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v : Pl D, (∀ a, a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v)) ∧ (∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v), (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v) ∧ (∀ (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s, s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v)) ∧ (∀ n : ℤ, ∀ s, s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v) ∧ (∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ∧ (∀ 𝔞 : FI D, 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v)) ∧ ∀ (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := fun D ψ hψ v =>
  ⟨GlobalTheory.T.unitIdealCompletionAtPlace_eq_integralAdelesAtPlace D v, GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v, GlobalTheory.T.mem_spanSingleton_mul_idealCompletion_iff D v, fun n s => GlobalTheory.T.periodIdealZpow_completion_adeleConj_iff D v n s,
    GlobalTheory.T.inverseDifferentCompletion_iff_characterDual D ψ hψ v, GlobalTheory.T.fractionalIdeal_locallyPrincipal_adelic D v, GlobalTheory.T.mem_scaledLatticeCompletion_iff_polarisationInverse D v⟩

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharUnramifiedAtQuotientSameResidualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharUnramifiedAt_quotient_same_residual : ∀ (D : D7) (c₁ c₂ : (AE D)ˣ →* Circle) (H₁ H₂ : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), ChrEq c₁ H₁ → ChrEq c₂ H₂ → IsRes H₁ PP ξ → IsRes H₂ PP ξ → GlobalTheory.LFun.UnrAt (F := D.host.F) (c₁ * c₂⁻¹) PP := by
  first | exact @GlobalTheory.ResUnr.unrAt_div_of_isRes | exact GlobalTheory.ResUnr.unrAt_div_of_isRes | (intros; apply GlobalTheory.ResUnr.unrAt_div_of_isRes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelCharacterEqBesselCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexZeroLevelCharacter_eq_besselCharacter : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = psiBes c.ψ (c.bes 0 D.R.rS h0).d 1 (vecB (c.bes 0 D.R.rS h0).o (c.bes 0 D.R.rS h0).ζ) n := by
  first | exact @GlobalTheory.LevZeroChar.levChi_eq_psiBes | exact GlobalTheory.LevZeroChar.levChi_eq_psiBes | (intros; apply GlobalTheory.LevZeroChar.levChi_eq_psiBes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvHaarVolumeToRealEqRelIndexIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_haarVolume_toReal_eq_relIndex_integral : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GlobalTheory.QTw.QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : GlobalTheory.QTw.QExt G χ) (j : ℕ) (H : Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)), H ≤ KO G.k _ → MeasurableSet (H : Set (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)) → H.relIndex (KO G.k _) ≠ 0 → ((((E.m j H).toReal)⁻¹ : ℝ) : ℂ) = (H.relIndex (KO G.k _) : ℂ) := by
  first | exact @GlobalTheory.QTw.QExt.m_inv_toReal_eq_relIndex | exact GlobalTheory.QTw.QExt.m_inv_toReal_eq_relIndex | (intros; apply GlobalTheory.QTw.QExt.m_inv_toReal_eq_relIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelCompIdempotentSplitTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPlaceModel_comp_idempotentSplitTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensL b (halfInd b Λ)) := by
  first | exact @GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf | exact GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf | (intros; apply GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf <;> assumption)
end

