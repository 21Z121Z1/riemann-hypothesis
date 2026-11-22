import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovGmin

def Hyp (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Prop :=
  LawsJ T ∧ 1 ≤ (T.Q.Dw j).p ∧ 1 ≤ (T.Q.Dw j).q ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧ InR D j ∧ Y.Good e o ∧
    1 ≤ Lb ∧ Real.log Y.d.l₂.M ≤ 30 * Lb ∧ fieldSz D.host.E ≤ 3 * Lb ∧ Real.log (D.R.f * D.R.r) ≤ Lb ∧
    o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 ∧ Dom a n ∧ Even n ∧ 8 * D.R.f * D.R.r + 4 ≤ n ∧
    (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p →
      ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) ∧
    Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb

def badC {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) : ℕ := D.host.QS * D.host.q * D.host.d * Y.d.l₂.M

def thFam {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) (nab : NabV Y.d.Xo₂ Y.d.c₂) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (n : ℕ) (ρ : ℝ) : Set (Y.V (wtZ a n)) :=
  {y | ∃ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F),
    Submodule.span (𝓞 D.host.E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt (badC Y) ∧ La.TrivAt Y.d.l₂.M ∧
      La.LevOK N Y.d.l₂.M ∧ P ∈ harmL Y.d.c₂ La a ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm Y.d.c₂ P ≤ ρ ∧
      ∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R),
        thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')}

end GlobalTheory.CovGmin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H}

theorem conjEmb_rt_of_not {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    conjEmb τ (H.rt : E) = H.rt0 := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE]; simp
  have hneg : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left h
  have hre : H.rt0.re = 0 := by
    have h2 := H.sqrt_neg_disc_sq
    have hr := congrArg Complex.re h2
    have hi := congrArg Complex.im h2
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im] at hr hi
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    by_contra hne
    have him : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [him] at hr
    nlinarith [mul_self_nonneg H.rt0.re]
  show (starRingEnd ℂ) (τ (H.rt : E)) = H.rt0
  rw [hneg]
  apply Complex.ext <;> simp [hre]

theorem psi_or_conj (σ : E →+* ℂ) : (∃ τ : Psi H, σ = τ.1) ∨ ∃ τ : Psi H, σ = conjEmb τ.1 := by
  by_cases h : σ (H.rt : E) = H.rt0
  · exact Or.inl ⟨⟨σ, h⟩, rfl⟩
  · exact Or.inr ⟨⟨conjEmb σ, conjEmb_rt_of_not h⟩, (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm⟩

theorem psi_nonempty : Nonempty (Psi H) := by
  have : 0 < Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact Module.finrank_pos
  obtain ⟨σ⟩ := Fintype.card_pos_iff.1 this
  rcases psi_or_conj (H := H) σ with ⟨τ, -⟩ | ⟨τ, -⟩ <;> exact ⟨τ⟩

theorem sum_mult : ∑ τ : E →+* ℂ, Dw.mult τ = (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) := by
  classical
  set P := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => τ (H.rt : E) = H.rt0) with hP
  set Q := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => ¬ τ (H.rt : E) = H.rt0) with hQ
  have hcard : Q.card = P.card := by
    refine Finset.card_nbij' conjEmb conjEmb ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact conjEmb_rt_of_not ha
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact GlobalTheory.AllWt.conj_not_mem ⟨a, ha⟩
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
  have htot : P.card + Q.card = Module.finrank ℚ E := by
    rw [← NumberField.Embeddings.card E ℂ, ← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = P.card * Dw.p + Q.card * Dw.q := by
    simp only [Datum.mult]
    rw [Finset.sum_ite]
    simp [Finset.sum_const, hP, hQ]
  rw [hsum, hcard, ← htot, hcard, ← two_mul, Nat.mul_div_cancel_left _ (by norm_num)]
  ring

variable (Dw) in

abbrev thExpZ (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℤ :=
  (GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ)).1

theorem thExpZ_big (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : i < Dw.p) :
    thExpZ Dw u n (τ.1, i) = u τ ⟨i, by omega⟩ + 1 - u τ ⟨Dw.p - 1, by omega⟩ := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_big _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos (show 0 < Dw.p by omega)]
  ring

theorem thExpZ_big_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.p ≤ i) :
    thExpZ Dw u n (τ.1, i) = 0 := by
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_pos τ.2, dif_neg (not_lt.2 hi)]

theorem thExpZ_small (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (hp : 0 < Dw.p) (τ : Psi H) (i : ℕ) (hi : i < Dw.q) :
    thExpZ Dw u n (conjEmb τ.1, i) =
      u τ ⟨Dw.p - 1, by omega⟩ - u τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ - 2 * ((n / 2 : ℕ) : ℤ) - 1 := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_small _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos hp]
  ring

theorem thExpZ_small_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.q ≤ i) :
    thExpZ Dw u n (conjEmb τ.1, i) = 0 := by
  have h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by
    rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_neg (GlobalTheory.AllWt.conj_not_mem τ), dif_pos h', dif_neg (not_lt.2 hi)]

theorem thA_dominant_lastPos_degree (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (b : ℝ) (hp : 1 ≤ Dw.p)
    (hn : Even n) (hu : ∀ τ, Antitone (u τ))
    (hgap : ∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j)
    (hb : ∀ τ i, |(u τ i : ℝ)| ≤ b) :
    Formalism.L2.Pj.Dom (thA Dw u n) n ∧
      Formalism.L2.Pj.wtZ (thA Dw u n) n =
        GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧
      Formalism.L2.Pj.LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧
      (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := by
  have hp0 : 0 < Dw.p := hp
  obtain ⟨τ0⟩ := psi_nonempty (H := H)
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb τ0 ⟨0, by omega⟩)
  have hup : ∀ τ i, (u τ i : ℝ) ≤ b := fun τ i => (le_abs_self _).trans (hb τ i)
  have hlo : ∀ τ i, -b ≤ (u τ i : ℝ) := fun τ i => by
    have := neg_abs_le (u τ i : ℝ); linarith [hb τ i]
  have hm : 2 * ((n / 2 : ℕ) : ℤ) = n := by obtain ⟨k, rfl⟩ := hn; omega

  have F1 : ∀ x, 0 ≤ thExpZ Dw u n x := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ i (by omega)]
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi]
        have h1 := hu τ (show (⟨Dw.p, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from
          Fin.mk_le_mk.2 (by omega))
        have h2 := hgap τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p, by omega⟩ (by simp; omega) rfl
        omega
      · rw [thExpZ_small_ge u n τ i (by omega)]

  have F2 : ∀ x, (thExpZ Dw u n x : ℝ) ≤ 2 * b + 1 := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]; push_cast
        linarith [hup τ ⟨i, by omega⟩, hlo τ ⟨Dw.p - 1, by omega⟩]
      · rw [thExpZ_big_ge u n τ i (by omega)]; push_cast; linarith
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi, hm]; push_cast
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith [hup τ ⟨Dw.p - 1, by omega⟩, hlo τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩]
      · rw [thExpZ_small_ge u n τ i (by omega)]; push_cast; linarith

  have F3 : ∀ σ i, thExpZ Dw u n (σ, i + 1) ≤ thExpZ Dw u n (σ, i) := by
    intro σ i
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i + 1 < Dw.p
      · rw [thExpZ_big u n τ _ hi, thExpZ_big u n τ i (by omega)]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨i + 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ (i + 1) (by omega)]; exact F1 _
    · by_cases hi : i + 1 < Dw.q
      · rw [thExpZ_small u n hp0 τ _ hi, thExpZ_small u n hp0 τ i (by omega)]
        have := hu τ (show (⟨Dw.p + (Dw.q - 1 - (i + 1)), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
          ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_small_ge u n τ (i + 1) (by omega)]; exact F1 _
  have hcast : ∀ x, (thA Dw u n x : ℝ) = (thExpZ Dw u n x : ℝ) := fun x => by
    have h := Int.toNat_of_nonneg (F1 x)
    show (((thExpZ Dw u n x).toNat : ℕ) : ℝ) = _
    rw [← h]; norm_cast
  have hbound : ∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1 := fun x => (hcast x).trans_le (F2 x)
  refine ⟨⟨fun σ => antitone_nat_of_succ_le fun i => Int.toNat_le_toNat (F3 σ i), hn⟩, ?_, ?_, hbound, ?_⟩
  · refine Prod.ext (funext fun x => ?_) ?_
    · exact Int.toNat_of_nonneg (F1 x)
    · show (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ)
      omega
  · intro σ hσ _
    have hmul : Dw.mult σ = Dw.p := if_pos hσ
    rw [hmul]
    have h1 : thExpZ Dw u n (σ, Dw.p - 1) = 1 :=
      (thExpZ_big u n ⟨σ, hσ⟩ (Dw.p - 1) (by omega)).trans (by ring)
    show 0 < (thExpZ Dw u n (σ, Dw.p - 1)).toNat
    rw [h1]; decide
  · have hDF : (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (2 * b + 1) := by
      unfold Formalism.L2.Pj.DF; push_cast
      refine Finset.sum_le_sum fun τ _ => ?_
      calc ∑ i : Fin (Dw.mult τ), (thA Dw u n (τ, i) : ℝ) ≤ ∑ _i : Fin (Dw.mult τ), (2 * b + 1) :=
            Finset.sum_le_sum fun i _ => hbound (τ, i)
        _ = _ := by simp [mul_add]
    rw [← Finset.sum_mul] at hDF
    have hs : (∑ τ : E →+* ℂ, (Dw.mult τ : ℝ)) =
        ((Module.finrank ℚ E / 2 : ℕ) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, sum_mult, Nat.cast_mul]
    rw [hs] at hDF
    exact hDF

end GlobalTheory.RefSum

example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : Weight Dw) (n : ℕ) (b : ℝ), 1 ≤ Dw.p → Even n → (∀ τ, Antitone (u τ)) → (∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j) → (∀ τ i, |(u τ i : ℝ)| ≤ b) → Dom (thA Dw u n) n ∧ wtZ (thA Dw u n) n = wtOf Dw (u + parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧ LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧ (DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := GlobalTheory.RefSum.thA_dominant_lastPos_degree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlaces
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.ThetaBaseMove

open Formalism.IndefR.Fin.LevelGroupLemmas

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem heisO_smul' (u : WO S T) (c : ℂ) (g : WO S T → ℂ) : heisO ψ S T u (c • g) = c • heisO ψ S T u g := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_smul (c : ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (c • g) := by
  refine ⟨fun γ w => ?_, ?_, hg.cont.const_smul c, fun k L hL h0 w => (hg.smooth k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [hg.quasi]; ring
  · obtain ⟨U, hU, h⟩ := hg.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul', h u hu h0]⟩

theorem isPlaceModel_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ)) (g : GA D S) (h : GA D T) (c : ℂ)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) f₀) (c • (om (g, h)).comp Tm) where
  trans Φ hΦ x hx := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.trans Φ hΦ x hx, LinearMap.comp_apply,
      hW.om_heis g h x (Tm Φ) (hth Φ hΦ), hfx x (Or.inl hx), heisO_smul']
  modul Φ hΦ y hy := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.modul Φ hΦ y hy, LinearMap.comp_apply,
      hW.om_heis g h y (Tm Φ) (hth Φ hΦ), hfx y (Or.inr hy), heisO_smul']
  vac := by rw [LinearMap.smul_apply, LinearMap.comp_apply, hTm.vac]

theorem isThetaAt_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hth : ∀ f₀, IsThetaFunO ψ S T f₀ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm →
      ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ))
    {b Φ f : WO S T → ℂ} (hb : IsThetaFunO ψ S T b) (g : GA D S) (h : GA D T) {c : ℂ} (hc : c ≠ 0)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 b Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) b) Φ (c • om (g, h) f) := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  refine ⟨⟨_, isPlaceModel_move hW hTm (hth b hb Tm hTm) g h c hfx⟩, fun T' hT' => ?_⟩
  have hfx' : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g⁻¹ h⁻¹ x = x := fun x hx => by
    conv_lhs => rw [← hfx x hx]
    rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
  have k1 : ∀ v, om (g⁻¹, h⁻¹) (om (g, h) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have k2 : ∀ v, om (g, h) (om (g⁻¹, h⁻¹) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have hm := isPlaceModel_move hW hT' (hth _ (theta_smul c (hW.om_pres _ _ hb)) T' hT') g⁻¹ h⁻¹ c⁻¹ hfx'
  rw [map_smul, k1, smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
  have e1 : f = _ := hall _ hm
  rw [e1, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, k2, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem actO_fix_of_orth {a e : AE D} {z : GA D S} (hz : SuppAt a S z) (h0 : e * (a + cA D a) = 0) {x : WO S T}
    (hx : IsHalf e x) : actO S T z⁻¹ 1 x = x := by
  rw [actO_eq, inv_inv, mt_one', Matrix.one_mul]
  have : HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z - 1) = 0 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← hx k j, ← hz j l]
    linear_combination (x k j * (mt S z - 1) j l) * h0
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this

end General

theorem thAt_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Sa ⊆ R.Q t → St ⊆ R.Q t → Disjoint Sa St → ∀ (eg ea et : AE D) (fg b Φ f : WO (Vc D i) (Wc D i) → ℂ) (z : GA D (Vc D i)) (c : ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) b → SuppAt ea (Vc D i) z → c ≠ 0 → ThAt R i (cA D et) b Φ f → ThAt R i (cA D et) (c • R.ωP i t (z⁻¹, 1) b) Φ (c • R.ωP i t (z⁻¹, 1) f) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t _hV Sa St hSa hSt hd eg ea et fg b Φ f z c hg ha ht hfg hb hz hc hf
  obtain ⟨⟨hψ, hvac⟩, e, he, -⟩ := hC.thP.vP i t
  have hW := (GlobalTheory.OnCmp.kerDat_tuple (i := i) hC.lev hC.thP t).weil
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hsp : SplitSet (R.Q t) := SplitSet.mono ⟨e, he⟩ (by convert Finset.subset_union_right)
  have hth : ∀ {a : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum a P → ∀ f₀, IsThetaFunO R.ψ (Vc D i) (Wc D i) f₀ → ∀ Tm,
      IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D a)
        (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 f₀ Tm →
      ∀ Ψ, IsSBHalf (cA D a) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ →
        IsThetaFunO R.ψ (Vc D i) (Wc D i) (Tm Ψ) := by
    intro a P h f₀ hf₀ Tm hTm Ψ hΨ
    exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ hSV.1 hSW.1 (by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self h])
      (by rw [← map_mul, h.2, map_zero]) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart h)) hf₀ Tm hTm Ψ hΨ
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBa := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    Sa (fun y => omegaQ Sa (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  have hfgθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) fg := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hfg
    rw [hall Tm hTm]
    exact hth hg _ hvac.theta Tm hTm _ hSBg
  have hbθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) b := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hb
    rw [hall Tm hTm]
    exact hth ha _ hfgθ Tm hTm _ hSBa
  have o1 : et * ea = 0 := by
    rw [← idem_eq ht, ← idem_eq ha, idem, idem, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq =>
      hsp.mul_eq_zero (hSt hp) (hSa hq) fun e => Finset.disjoint_left.1 hd hq (e ▸ hp)
  have o2 : et * cA D ea = 0 := by
    rw [← idem_eq ht, ← idem_eq ha, idem, idem, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => hsp.mul_conj (hSt hp) (hSa hq)
  have o3 : et * (ea + cA D ea) = 0 := by rw [mul_add, o1, o2, add_zero]
  have o4 : cA D et * (ea + cA D ea) = 0 := by
    have := congrArg (cA D) o3
    rwa [map_mul, map_add, GlobalTheory.LatVac.cA_cA, map_zero, add_comm] at this
  refine isThetaAt_move hW (hth ht) hbθ z⁻¹ 1 hc (fun x hx => ?_) hf
  rcases hx with hx | hx
  · exact actO_fix_of_orth hz o4 hx
  · rw [GlobalTheory.LatVac.cA_cA] at hx
    exact actO_fix_of_orth hz o3 hx

end GlobalTheory.ThetaBaseMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapIdentityEveryNormalisedFamily
section
set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapAll

theorem identityRow_of_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ i, GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht hio i Tp tup O _ hO
  obtain ⟨cc, -, u, -, -, -, h⟩ := GlobalTheory.T.exists_unitModulus_constants_equivariant_dictionary hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i Tp tup O hO
  exact ⟨u • cc, 1, h⟩

end GlobalTheory.OneMapAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem thetaRules_exist_and_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a → ∀ f ∈ thGen Xo c nab a n, f ∈ cuspW Xo c U (wtZ a n) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro r U hr hU nab hn
  refine ⟨GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw l Xo c nab hn, ?_⟩
  intro a n hd hl f hf
  rw [GlobalTheory.AllWt.cuspW_wtZ, ← Formalism.L2.PjFree.cusp_ofPj]
  exact GlobalTheory.Dict.thInCusp_cusp GlobalTheory.chartIndependence_unconditional E H Dw l Xo c r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
    (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj _).2 (hU σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))) nab hn a n hd hl f hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRationalityAtPlace
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem traceOfAt : TraceOfAt := by
  refine AtTw.of_forall fun Fm x hx i p hR hM w hw j => ?_
  intro ρ hρ hpin hlev h P
  have hL := GlobalTheory.BigOn.links2_of_rows _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have key := GlobalTheory.T.thetaTraceLevelCompatible_proof _ _ _ _ _ _ (R2 p) (F2 p) hC j _ (hρ.base _ j _) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)))
    ?_ ?_ ?_ _ (hρ.weil_base _ j _) h P
  · exact key.symm
  · intro g Q hQ hQ' a c
    have e := hpin.grp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ((p.R.eG.trans p.cG) g) Q hQ hQ' a c
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at e
    exact e
  · intro g
    exact mem_level_iff hM.2.2 hlev _ j _ g
  · intro u hu
    refine (level_chi hM.2.2 hρ hlev _ j _ u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl

end GlobalTheory.BigOn.Exp.SerBase
end
end

