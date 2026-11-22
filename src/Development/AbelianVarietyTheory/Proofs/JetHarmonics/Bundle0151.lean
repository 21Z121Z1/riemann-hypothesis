import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0034
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0041
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0110
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0147
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0148

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InverseEntrySmulCapelliEigenfunctionSum
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_inv_entry (k r : ℕ) (c j : Fin (2 * r + k + 1)) :
    B.CkOn ⊤ (B.GV k r) (fun y : B.Mat k r => y⁻¹ c j) := by
  intro g₀ _
  refine ⟨Set.univ, fun g => Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c g, isOpen_univ, trivial,
    (Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c).contDiff.contDiffOn, fun g _ hg => ?_⟩
  show g⁻¹ c j = Matrix.mulVec (Hpk k r * g.conjTranspose * Hpk k r) (Pi.single j 1) c
  rw [← Formalism.FourierDecayAlt.P.JCx2.mn_inv_gv hg]
  simp

theorem inCC_inv_entry_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (c j : Fin (2 * r + k + 1)) {A : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.InCC A m F) :
    B.InCC (A - 1) m (fun g : B.Mat k r => g⁻¹ c j • F g) := by
  have hg : Formalism.FourierDecayAlt.P.JCx2.pdGood Wp Wq 1 (fun g : B.Mat k r => g⁻¹ c j) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_good_congr (fun g _ => by simp)
      (Formalism.FourierDecayAlt.P.JCx2.pd_good_inv (Wp := Wp) (Wq := Wq) (Pi.single j 1) c)
  obtain ⟨K, -, hK⟩ := hg.2 (A - 1) m
  obtain ⟨b, hb⟩ := hF
  exact ⟨K * b, hK F b (by rw [Nat.cast_one, sub_add_cancel]; exact hb)⟩

theorem inv_entry_smul_eigen_split : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), Function.Injective lam → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ Fi : Fin (2 * r + k + 1) → B.Mat k r → (Wq →L[ℂ] Wp), (∀ t, (B.CkOn ⊤ (B.GV k r) (Fi t) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi t))) ∧ (∀ t, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi t) g = ((∏ s, (Y + (lam s - if s = t then 1 else 0)) : ℝ) : ℂ) • (Fi t) g)) ∧ ∀ g ∈ B.GV k r, g⁻¹ i j • f g = ∑ t, Fi t g := by
  intro k r Wp Wq _ _ _ _ _ _ lam A i j f hlam hf heig
  obtain ⟨V, W, _, _, _, _, E, E', ι, ev, mul, hE, hE', hι, hq, hsm, hext, hcc, hex, -, hqC, hmul⟩ :=
    GlobalTheory.capelli_module_model k r Wp Wq lam A
  obtain ⟨w, hw⟩ := hex f hf heig
  let x : Fin (2 * r + k + 1) → Module.End ℂ V := fun c => mul (fun y : B.Mat k r => y⁻¹ c j)
  have hx : ∀ c v, ∀ g ∈ B.GV k r, ev (x c v) g = g⁻¹ c j • ev v g :=
    fun c => (hmul _ (ckOn_inv_entry k r c j)).1
  have hcomm : ∀ a b c, E a b * x c = x c * E a b - if a = c then x b else 0 := by
    intro a b c
    ext v
    refine hext _ _ fun g hg => ?_
    have h1 := (hmul _ (ckOn_inv_entry k r c j)).2 a b v g hg
    rw [GlobalTheory.eh_inv_entry k r a b c j g hg] at h1
    rw [Module.End.mul_apply, LinearMap.sub_apply, map_sub, Pi.sub_apply, Module.End.mul_apply, hx _ _ g hg]
    refine h1.trans ?_
    split_ifs with h
    · rw [hx _ _ g hg, neg_smul, sub_eq_add_neg]
    · simp
  have hinj : Function.Injective
      (fun s => ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2)) := by
    intro s t h
    apply hlam
    have h' : (lam s : ℂ) = lam t := sub_left_inj.1 h
    exact_mod_cast h'
  obtain ⟨v, hv1, hv2⟩ := GlobalTheory.covector_multiplier_shift V W _ E E' ι x _ hE hE' hι hinj hq hcomm i w
  refine ⟨fun t => ev (∑ a, x a (ι (v t a))), fun t => ⟨hsm _, fun m => ?_⟩, fun t Y g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum (A := A - 1) (m := m) Finset.univ
      (fun a (g : B.Mat k r) => g⁻¹ a j • ev (ι (v t a)) g)
      (fun a _ => inCC_inv_entry_smul a j (hcc (v t a) m))
    refine ⟨b, Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => ?_) hb⟩
    beta_reduce
    rw [map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (hx _ _ g hg).symm
  · rw [← hqC _ _ g hg, hv2, map_smul, Pi.smul_apply]
    congr 1
    push_cast
    refine Finset.prod_congr rfl fun s _ => ?_
    split_ifs <;> push_cast <;> ring
  · rw [← hw g hg, ← hx i _ g hg, hv1, map_sum, Finset.sum_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateAndRowConditionTwoPairsOfPlacesStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonDeg_raw_pairData_and_rankMaximal : (∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), NDG Y → NonDeg (Y.raw p) V) ∧ RankMaximalOfNondegenerate := by
  first | exact @GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces | exact GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces | (intros; apply GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowConditionTwoSelfConjugateOfNonDegenerateStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankMaximal_rawSelf_of_ndg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), NDG Y → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc := by
  first | exact @GlobalTheory.RowAtSelf.rowCondition_two_selfConjugate_of_nonDegenerate | exact GlobalTheory.RowAtSelf.rowCondition_two_selfConjugate_of_nonDegenerate | (intros; apply GlobalTheory.RowAtSelf.rowCondition_two_selfConjugate_of_nonDegenerate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SizesBoundAtTwoFirstRowsWeightsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_bound_at_two_first_rows_weights : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (Q : Par D), Q.Pins → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ C : ℝ, 1 ≤ C → ∀ j, InR D j → ∃ Ap : ℝ, 0 ≤ Ap ∧ (∀ τ, InPsi Q.H τ → (wtA (lR Tp hK j) (τ, 0) : ℝ) ≤ Ap) ∧ (open Classical in (Tp.TO : ℝ) * ((D.R.f : ℝ) * (Q.Dw j).q * (1 + vd2 D / 2) * Ap + (Q.Dw j).q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi Q.H τ), (wtA (lR Tp hK j) (τ, 0) : ℝ)) ≤ C * D.R.m * (2 + vd2 D) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz))) := by
  first | exact @GlobalTheory.RunDepth.sizes_bound_two | exact GlobalTheory.RunDepth.sizes_bound_two | (intros; apply GlobalTheory.RunDepth.sizes_bound_two <;> assumption)
end

