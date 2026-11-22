import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometry
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma mat_lact_castFr_eq_map_mul {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)}
    (hΨ : Ψ = Ψ') (a : GL (Fin r) E) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (τ : E →+* ℂ) (hτ : τ ∈ Ψ')
    (hτ₀ : τ ∈ Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr hΨ x)) ⟨τ, hτ⟩ =
      (a : Matrix (Fin r) (Fin r) E).map τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ₀⟩ := by
  rfl

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma emb_mulVec_eq_map_mulVec_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (A *ᵥ v) = (A.map τ) *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
  funext k
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma col_mul_eq_mulVec_col' {r : ℕ} (A M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.col (A * M) j = A *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.col M j := by
  funext k
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mulVec, dotProduct, Matrix.mul_apply]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in

theorem _root_.GlobalTheory.GeoLevel.perFr_lact_of_isMatch : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (a : GL (Fin r) E)
    (h : _root_.GlobalTheory.LevelCusp.IsMatch X X' a) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (v : Fin r → E)
    (τ : E →+* ℂ) (i : ℕ),
    _root_.Formalism.L2.PjFree.perFr X' (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr h.psi x))
        ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = _root_.Formalism.L2.PjFree.perFr X x v τ i := by
  intro E _ _ _ r X X' a h x v τ i
  have hΨ := h.psi
  have hp := h.p0
  have hA : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    have h₀ := (Matrix.isUnits_det_units a).map τ
    rwa [RingHom.map_det] at h₀
  unfold _root_.Formalism.L2.PjFree.perFr
  by_cases hτ : τ ∈ X.Ψ
  · have hτ' : τ ∈ X'.Ψ := hΨ ▸ hτ
    rw [dif_pos hτ', dif_pos hτ]
    by_cases hi : X.p0 + i < r
    · have hi' : X'.p0 + i < r := hp ▸ hi
      rw [dif_pos hi', dif_pos hi]
      have hfin : (⟨X'.p0 + i, hi'⟩ : Fin r) = ⟨X.p0 + i, hi⟩ := Fin.ext (by simp [hp])
      rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x τ hτ' hτ, emb_mulVec_eq_map_mulVec_emb, Matrix.mul_inv_rev,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
    · have hi' : ¬ X'.p0 + i < r := hp ▸ hi
      rw [dif_neg hi', dif_neg hi]
  · have hτ' : τ ∉ X'.Ψ := hΨ ▸ hτ
    rw [dif_neg hτ', dif_neg hτ]
    by_cases hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X.Ψ
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X'.Ψ := hΨ ▸ hσ
      rw [dif_pos hσ', dif_pos hσ]
      by_cases hj : X.p0 - 1 - i < r
      · have hj' : X'.p0 - 1 - i < r := hp ▸ hj
        rw [dif_pos hj', dif_pos hj]
        have hfin : (⟨X'.p0 - 1 - i, hj'⟩ : Fin r) = ⟨X.p0 - 1 - i, hj⟩ := Fin.ext (by simp [hp])
        rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x _ hσ' hσ, col_mul_eq_mulVec_col', emb_mulVec_eq_map_mulVec_emb]
        exact h.hermC_eq _ _ _
      · have hj' : ¬ X'.p0 - 1 - i < r := hp ▸ hj
        rw [dif_neg hj', dif_neg hj]
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∉ X'.Ψ := hΨ ▸ hσ
      rw [dif_neg hσ', dif_neg hσ]

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.ConjAtPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_of_lt_one {w : HeightOneSpectrum (𝓞 E)} (x : w.adicCompletion E) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) {z : w.adicCompletion E} (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (nhds 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_of_lt_one z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  rw [map_pow] at hN
  exact absurd hN (not_lt.2 (one_le_pow₀ hc))

theorem conjSrc_eq_of_cont (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s)
    (he : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hmem : ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ Valued.v (algebraMap E (w.adicCompletion E) (a : E)) < 1 := by
    intro a
    rw [hval, HeightOneSpectrum.valuation_lt_one_iff_mem]
  have hdir : ∀ x y : 𝓞 E, (y : E) = IsCMField.complexConj E (x : E) → x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    rw [hmem] at hx ⊢
    rw [hxy, ← he]
    exact lt_one_of_continuous s hs hx
  have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.SplitPts.conjE E) w w := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    refine ⟨hdir x y hxy, hdir y x ?_⟩
    rw [show (GlobalTheory.SplitPts.conjE E) (x : E) = IsCMField.complexConj E (x : E) from rfl] at hxy
    rw [hxy, IsCMField.complexConj_apply_apply]
  exact (eq_conjSrc hc).symm

theorem conjSrc_eq_iff (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w ↔ ¬ IsSplitAt w := by
  refine ⟨fun h hs => (GlobalTheory.SplitPts.over_split hs).1 h, fun h => ?_⟩
  by_contra hne
  apply h
  exact ⟨conjSrc (GlobalTheory.SplitPts.conjE E) w, hne,
    (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))⟩

theorem ext_of_cont {v w : HeightOneSpectrum (𝓞 E)} (s t : v.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) (ht : Continuous t)
    (hse : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hte : ∀ x : E, t (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) : s = t :=
  RingHom.ext fun y => congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hs ht
    (funext fun k => (hse k).trans (hte k).symm)) y

theorem cont_of_val {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s :=
  GlobalTheory.Mem.Chr.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective E w) s hv

theorem cj_spec (w : Pl E)
    (h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    Continuous (cj w) ∧ ∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  unfold cj
  rw [dif_pos h]
  exact h.choose_spec

theorem cj_of_not (w : Pl E)
    (h : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    cj w = RingHom.id _ := by
  unfold cj
  rw [dif_neg h]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, Continuous (cj w) ∧ (∀ x, cj w (cj w x) = x) ∧ (∀ x, Valued.v (cj w x) = Valued.v x) ∧ (¬ IsSplitAt w → (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ (∃ ϖ q, IsUnramInv ϖ (cj w) q ∧ qV E w = q ^ 2) ∧ (∀ x : Af E, pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj w (pLoc E w x)) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → ¬ IsSplitAt w := by
  intro E _ _ _ hU w
  by_cases hsp : IsSplitAt w
  · have hno : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
      rintro ⟨s, hs, he⟩
      exact (GlobalTheory.SplitPts.over_split hsp).1 (conjSrc_eq_of_cont w s hs he)
    have hid := cj_of_not w hno
    refine ⟨by rw [hid]; exact continuous_id, fun x => by rw [hid]; rfl, fun x => by rw [hid]; rfl,
      fun h => absurd hsp h, fun s hv he _ => hno ⟨s, cont_of_val s hv, he⟩⟩
  · obtain ⟨s0, ϖ, q, he0, hU0⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv E w (hU w) hsp
    have hc0 : Continuous s0 := cont_of_val s0 hU0.2.1
    obtain ⟨hcj, hecj⟩ := cj_spec w ⟨s0, hc0, he0⟩
    have heq : cj w = s0 := ext_of_cont _ _ hcj hc0 hecj he0
    have hsrc : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := (conjSrc_eq_iff w).2 hsp
    refine ⟨hcj, fun x => by rw [heq]; exact hU0.1 x, fun x => by rw [heq]; exact hU0.2.1 x,
      fun _ => ⟨hecj, ⟨ϖ, q, by rw [heq]; exact hU0, ?_⟩, fun x => ?_,
        fun s hv he => ext_of_cont _ _ (cont_of_val s hv) hcj he hecj⟩, fun _ _ _ => hsp⟩
    · exact (Formalism.UG.P.tjcosets_card_residue w).symm.trans hU0.2.2.2.2.2.2
    · rw [pLoc_conjFin]
      have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
          Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
          f (pLoc E v x) = cj w (pLoc E w x) := by
        rintro v rfl f hf hfe
        rw [ext_of_cont f (cj v) hf hcj hfe hecj]
      exact key _ hsrc _ (conjLoc_spec _ w).1 (conjLoc_spec _ w).2.1

end GlobalTheory.ConjAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectors
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct ContDiff

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7}

def algEntry (V : HSp D) (τ : D.what₂.Tau) (m j : Fin V.rank) : AlgInf V →ₗ[ℝ] ℂ where
  toFun u := (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ m j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contDiff_expEntry (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (τ : D.what₂.Tau) (m j : Fin V.rank) :
    ContDiff ℝ ∞ fun X : LieN V => algEntry V τ m j (NormedSpace.exp (jInf V X)) := by
  haveI : CompleteSpace (AlgInf V) := FiniteDimensional.complete ℝ (AlgInf V)
  haveI : FiniteDimensional ℝ (LieN V) := FiniteDimensional.of_injective (jInf V) (isLieData R).inj
  have h1 : ContDiff ℝ ∞ (NormedSpace.exp : AlgInf V → AlgInf V) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact (LinearMap.toContinuousLinearMap (algEntry V τ m j)).contDiff.comp
    (h1.comp (LinearMap.toContinuousLinearMap (jInf V)).contDiff)

theorem realEntries_mul_exp (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (g : GA D V) (X : LieN V) (p : D.what₂.Tau × Fin V.rank × Fin V.rank) :
    realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p =
      ∑ m, infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 m * algEntry V p.1 m p.2.2 (NormedSpace.exp (jInf V X)) := by
  have h2 := (isExpFam_expInf R X).2 p.1
  change infMat D.sp.cm.sig V.gram (θ p.1) (g * expInf θ V X) p.2.1 p.2.2 = _
  rw [R.2.2.2.1, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  change infMat D.sp.cm.sig V.gram (θ p.1) (expInf θ V X) m p.2.2 = (NormedSpace.exp (jInf V X) : AlgInf V) p.1 m p.2.2
  rw [exp_algInf, h2]
  rfl

theorem polyFun_mem_smF : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  intro D θ V R P g
  have hc : ∀ p : D.what₂.Tau × Fin V.rank × Fin V.rank,
      ContDiff ℝ ∞ fun X : LieN V => realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p := by
    intro p
    simp only [realEntries_mul_exp θ R]
    exact ContDiff.sum fun m _ => contDiff_const.mul (contDiff_expEntry θ R p.1 m p.2.2)
  change ContDiff ℝ ∞ fun X : LieN V => MvPolynomial.eval (realEntries θ V (g * expMap (jInf V) (secInf θ V) X)) P
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p n hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (hc n)

end GlobalTheory.CentralOps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialProductCoeffsCentral
section
open Matrix GlobalTheory.TorFin

noncomputable section

namespace GlobalTheory.IntModFac

open Polynomial

def sumPoly {S : Type} [Semiring S] (n : ℕ) (f : ℕ → S) : S[X] :=
  ∑ k ∈ Finset.range (n + 1), C (f k) * X ^ k

end GlobalTheory.IntModFac

namespace GlobalTheory

open Polynomial GlobalTheory.IntModFac

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdOfSpecialisations
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShortDiv

variable {F : Type} [Field F] {D N : ℕ}

noncomputable def lastSubst (l₀ : Fin N → F) : Fin (D + 1) × Fin N → MvPolynomial (Fin (D + 1) × Fin N) F :=
  fun p => if p.1 = Fin.last D then C (l₀ p.2) else X p

theorem eval_aeval_lastSubst (l₀ : Fin N → F) (x : Fin (D + 1) × Fin N → F)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval x (aeval (lastSubst l₀) f) = eval (fun p => if p.1 = Fin.last D then l₀ p.2 else x p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p q hp =>
    simp only [map_mul, hp, aeval_X, eval_X, lastSubst]
    split_ifs <;> simp

theorem replace_eq_join (l : Fin N → F) (x : Fin (D + 1) × Fin N → F) :
    (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l p.2 else x p) =
      join (fun i j => x (i.castSucc, j)) l := by
  funext ⟨i, j⟩
  induction i using Fin.lastCases with
  | last => simp [join]
  | cast i => simp [join, Fin.castSucc_ne_last]

theorem eval_last_zero {δ : ℕ} (hδ : 1 ≤ δ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (x : Fin (D + 1) × Fin N → F) :
    eval (fun p => if p.1 = Fin.last D then 0 else x p) f = 0 := by
  rw [eval_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  have hs := hf d hd (Fin.last D)
  have hne : (∑ j : Fin N, d (Fin.last D, j)) ≠ 0 := by simp only at hs; omega
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (Fin.last D, j)) (Finset.mem_univ _) ?_)
  simp [zero_pow hj]

theorem pow_dvd_of_specialisations (F : Type) [Field F] [CharZero F] (D N δ b : ℕ) (f G : MvPolynomial (Fin (D + 1) × Fin N) F)
    (Q : MvPolynomial (Fin D × Fin N) F) (hδ : 1 ≤ δ) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (hirr : Irreducible f) (hQ : Q ≠ 0)
    (hG : ∀ s : Fin D → Fin N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → ∃ (E : Type) (_ : Field E)
      (_ : Algebra F E) (γ : E), ∀ l : Fin N → F,
        algebraMap F E (eval (join s l) G) = γ * algebraMap F E (eval (join s l) f) ^ b) :
    f ^ b ∣ G := by
  haveI : Infinite F := Infinite.of_injective Nat.cast Nat.cast_injective
  have hf0 : f ≠ 0 := hirr.ne_zero

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, eval x₀ f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (MvPolynomial.funext fun x => by simp [h x])
  set l₀ : Fin N → F := fun j => x₀ (Fin.last D, j) with hl₀
  set g := aeval (lastSubst l₀) f with hg
  set G₀ := aeval (lastSubst l₀) G with hG₀
  set Q' : MvPolynomial (Fin (D + 1) × Fin N) F :=
    rename (fun p : Fin D × Fin N => (p.1.castSucc, p.2)) Q with hQ'
  have hQ'0 : Q' ≠ 0 := by
    intro h
    apply hQ
    apply rename_injective _ _ (h.trans (map_zero _).symm)
    intro p q hpq
    simp only [Prod.mk.injEq, Fin.castSucc_inj] at hpq
    exact Prod.ext hpq.1 hpq.2

  have key : Q' * (G * g ^ b - f ^ b * G₀) = 0 := by
    apply MvPolynomial.funext
    intro x
    set s : Fin D → Fin N → F := fun i j => x (i.castSucc, j) with hs
    have hx : x = join s (fun j => x (Fin.last D, j)) := by
      rw [← replace_eq_join]
      funext p
      split_ifs with h
      · rw [← h]
      · rfl
    have hQx : eval x Q' = eval (fun p => s p.1 p.2) Q := by
      rw [hQ', eval_rename]; rfl
    simp only [map_mul, map_sub, map_pow, map_zero]
    by_cases hq : eval (fun p => s p.1 p.2) Q = 0
    · rw [hQx, hq, zero_mul]
    · obtain ⟨E, _, _, γ, hγ⟩ := hG s hq
      have h1 := hγ (fun j => x (Fin.last D, j))
      have h2 := hγ l₀
      rw [← hx] at h1
      have hgx : eval x g = eval (join s l₀) f := by rw [hg, eval_aeval_lastSubst, replace_eq_join]
      have hGx : eval x G₀ = eval (join s l₀) G := by rw [hG₀, eval_aeval_lastSubst, replace_eq_join]
      rw [hgx, hGx]
      have : eval x G * eval (join s l₀) f ^ b - eval x f ^ b * eval (join s l₀) G = 0 := by
        apply (algebraMap F E).injective
        simp only [map_sub, map_mul, map_pow, map_zero, h1, h2]
        ring
      rw [this, mul_zero]
  have heq : G * g ^ b = f ^ b * G₀ := by
    have := (mul_eq_zero.mp key).resolve_left hQ'0
    exact sub_eq_zero.mp this
  have hp : Prime f := hirr.prime

  have hndvd : ¬ f ∣ g := by
    rintro ⟨h, hh⟩
    have hg0 : g ≠ 0 := by
      intro h0
      have := congrArg (eval x₀) h0
      rw [hg, eval_aeval_lastSubst, map_zero] at this
      apply hx₀
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x₀ p) = x₀ := by
        funext p
        split_ifs with hp1
        · rw [hl₀]; simp only; rw [← hp1]
        · rfl
      rw [hpt] at this
      exact this
    apply hg0
    apply MvPolynomial.funext
    intro x
    have e1 : eval x g = eval (fun p => if p.1 = Fin.last D then 0 else x p) g := by
      rw [hg, eval_aeval_lastSubst, eval_aeval_lastSubst]
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x p) =
          (fun p => if p.1 = Fin.last D then l₀ p.2 else if p.1 = Fin.last D then 0 else x p) := by
        funext p
        split_ifs <;> rfl
      rw [hpt]
    rw [e1, hh, map_mul, eval_last_zero hδ f hf, zero_mul, map_zero]
  have hndvd' : ¬ f ∣ g ^ b := fun h => hndvd (hp.dvd_of_dvd_pow h)
  exact hp.pow_dvd_of_dvd_mul_right b hndvd' ⟨G₀, heq⟩

end GlobalTheory.HSShortDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLatti
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.Sys

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]

theorem word_succ {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    {t : ℕ} (u : Fin (t + 1) → Fin N → K) : word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

theorem word_zero {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    (u : Fin 0 → Fin N → K) : word mul u = 1 := by
  simp [word]

theorem mul_mem_V_succ (S : Sys F A) (hS : S.Hyp) {j : ℕ} (hj : j < S.T) (u : Fin S.N → F) {x : A} (hx : x ∈ S.V j) :
    S.mul u x ∈ S.V (j + 1) := by
  have key : ∀ m ∈ S.M j, ∀ u : Fin S.N → F, S.mul u (m : A) ∈ S.V (j + 1) := by
    intro m hm u
    have hu : u ∈ Submodule.span F (Set.range S.w.col) := hS.lat.spans ▸ Submodule.mem_top
    let L : (Fin S.N → F) →ₗ[F] A := (LinearMap.applyₗ (m : A)) ∘ₗ S.mul
    have hle : Submodule.span F (Set.range S.w.col) ≤ (S.V (j + 1)).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨g, -, hg⟩ := hS.stable j hj k m hm
      show L (S.w.col k) ∈ S.V (j + 1)
      simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply]
      rw [← hg]
      exact g.2
    exact hle hu
  let P : Submodule F (S.V j) := (S.V (j + 1)).comap (S.mul u ∘ₗ (S.V j).subtype)
  have hP : Submodule.span F (S.M j : Set (S.V j)) ≤ P := by
    rw [Submodule.span_le]
    intro m hm
    exact key m hm u
  have hx' : (⟨x, hx⟩ : S.V j) ∈ Submodule.span F (S.M j : Set (S.V j)) :=
    (hS.full j hj.le).span ▸ Submodule.mem_top
  exact hP hx'

theorem word_mem (S : Sys F A) (hS : S.Hyp) (j t : ℕ) (hjt : j + t ≤ S.T) :
    (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧
      ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x := by
  induction t with
  | zero =>
    refine ⟨fun u x hx => ?_, fun e x hx => ⟨x, hx, ?_⟩⟩
    · simpa [word_zero] using hx
    · simp [word_zero]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlt : j + t < S.T := by omega
    refine ⟨fun u x hx => ?_, fun e x hx => ?_⟩
    · rw [word_succ, Module.End.mul_apply]
      exact mul_mem_V_succ S hS hlt (u 0) (ih1 (fun i => u i.succ) x hx)
    · obtain ⟨g', hg', hg'e⟩ := ih2 (fun i => e i.succ) x hx
      obtain ⟨g, hg, hge⟩ := hS.stable (j + t) hlt (e 0) g' hg'
      refine ⟨g, hg, ?_⟩
      rw [word_succ, Module.End.mul_apply, hge, hg'e]

end GlobalTheory.HSShort.Sys

namespace GlobalTheory.HSShort

theorem wordMem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (j t : ℕ), j + t ≤ S.T → (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧ ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x :=
  fun _ _ _ _ _ _ _ _ S hS j t hjt => S.word_mem hS j t hjt

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieOneParameterIsRealOneParamSubgroupAdelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_one_parameter_isRealOneParamSubgroupAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  first | exact @GlobalTheory.UAut.isRealLine_oneP | exact GlobalTheory.UAut.isRealLine_oneP | (intros; apply GlobalTheory.UAut.isRealLine_oneP <;> assumption)
end

