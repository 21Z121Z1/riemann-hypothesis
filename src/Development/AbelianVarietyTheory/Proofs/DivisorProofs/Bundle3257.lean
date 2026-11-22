import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3241
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0806
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0029
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.BoxCubicalUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3195

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedChartEvalSquareVariablesSwapConstant
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.EvSquare

noncomputable def constAlg (σ : Type) (k : Type) [CommRing k] : MvPowerSeries σ k →ₐ[k] k :=
  { (constantCoeff : MvPowerSeries σ k →+* k) with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

theorem evA_zero (k : Type) [CommRing k] (σ : Type) [Finite σ] (f : MvPowerSeries σ k) :
    evA k (fun _ : σ => (0 : k)) (fun _ => IsNilpotent.zero) f = constantCoeff f := by
  have h := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ k (evA k (fun _ : σ => (0 : k)) (fun _ => IsNilpotent.zero))
    (constAlg σ k) (fun i => by rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact IsNilpotent.zero)
    (fun i => by rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; simp [constAlg])
  rw [h]; rfl

theorem main : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ n, (∀ f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[k] 1) ∧ (∀ f, c.ev₂ n (inR f) = 1 ⊗ₜ[k] c.ev n f) ∧ (∀ s, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s)) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n)) (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  intro p k _ d G c n
  have hX : ∀ t, c.ev₂ n (X t) = c.x₂ n t := fun t => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate _ _ _ _ _ t
  have hN : ∀ t, IsNilpotent (c.ev₂ n (X t)) := fun t => by rw [hX]; exact c.nil₂ n t
  refine ⟨fun f => ?_, fun f => ?_, fun s => ?_, fun s => ?_⟩
  · have hy : ∀ i, IsNilpotent (c.x n i ⊗ₜ[k] (1 : G.A n)) := fun i => c.nil₂ n (Sum.inl i)
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (fun i => X (Sum.inl i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      Algebra.TensorProduct.includeLeft (c.x n) (c.nil n) _ hy (fun i => rfl) f
    unfold inL; rw [e1, ← e2]; rfl
  · have hy : ∀ i, IsNilpotent ((1 : G.A n) ⊗ₜ[k] c.x n i) := fun i => c.nil₂ n (Sum.inr i)
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (fun i => X (Sum.inr i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      Algebra.TensorProduct.includeRight (c.x n) (c.nil n) _ hy (fun i => rfl) f
    unfold inR; rw [e1, ← e2]; rfl
  · let g : G.A n ⊗[k] G.A n →ₐ[k] G.A n ⊗[k] G.A n :=
      (Algebra.TensorProduct.comm k (G.A n) (G.A n)).toAlgHom
    have hy : ∀ i, IsNilpotent (g (c.x₂ n i)) := fun i => (c.nil₂ n i).map g
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)))
      (fun i => by cases i <;> exact constantCoeff_X _) _ hy
      (fun i => by
        cases i with
        | inl i => rw [Sum.elim_inl, hX]; simp [g, Chart.x₂]
        | inr i => rw [Sum.elim_inr, hX]; simp [g, Chart.x₂]) s
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 (G.A n ⊗[k] G.A n)
      g (c.x₂ n) (c.nil₂ n) _ hy (fun i => rfl) s
    unfold Katz.swap at2
    rw [e1, ← e2]; rfl
  · let L : G.A n ⊗[k] G.A n →ₐ[k] k := Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n))
      (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _)
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 k
      L (c.x₂ n) (c.nil₂ n) (fun _ => (0 : k)) (fun _ => IsNilpotent.zero)
      (fun i => by
        cases i with
        | inl i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]
        | inr i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]) s
    change L (c.ev₂ n s) = _
    unfold Chart.ev₂; rw [e2, evA_zero]

end GlobalTheory.EvSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCohomologousEvenFormsAlgebraClosedStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbarCohomologousEvenForms_algebra_closed : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) , DbarCoh A 1 1 ∧ (∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w) ∧ ∀ (c : ℂ) (w w' z z' : A.Pt → Ev n), DbarCoh A w w' → DbarCoh A z z' → DbarCoh A (c • w) (c • w') ∧ DbarCoh A (w + z) (w' + z') ∧ DbarCoh A (w * z) (w' * z') := by
  first | exact @GlobalTheory.ChernCalc.dbarCoh_algebra | exact GlobalTheory.ChernCalc.dbarCoh_algebra | (intros; apply GlobalTheory.ChernCalc.dbarCoh_algebra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryBoundOfInputs
section
open GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.SumSize

theorem dictK_of_normSum (hP : GlobalTheory.FunPr.Hypotheses₂) (hI : ∀ D, GlobalTheory.NormSum.Inp D) : DictK := by
  obtain ⟨CF0, h⟩ := GlobalTheory.T.dictionary_size_bound hP hI
  refine ⟨CF0, fun CF hCF => ⟨0, fun ε C _ => ?_⟩⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ =>
    hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt⟩

end GlobalTheory.SumSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLab
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.IntLabel

section
variable {G X : Type} [AddCommGroup G] [AddCommGroup X] {N : ℕ} {Y : G → (Fin 8 → X) → Prop}

theorem yy_zero (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) : Y 0 0 := by
  obtain ⟨mu, hmu⟩ := h1 0
  have h2 := h4 0 0 mu mu hmu hmu
  rw [add_zero] at h2
  have hc := (h3 0 mu (mu + mu) hmu).1 h2
  refine (h3 0 mu 0 hmu).2 fun v => ?_
  obtain ⟨w, hw⟩ := hc v
  have e : mu v = N • w := add_left_cancel (a := mu v) (by simpa using hw)
  exact ⟨-w, by simp [e]⟩

theorem yy_neg (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a : G} {mu : Fin 8 → X} (ha : Y a mu) :
    Y (-a) (-mu) := by
  obtain ⟨mu', h'⟩ := h1 (-a)
  have h0 := h4 a (-a) mu mu' ha h'
  rw [add_neg_cancel] at h0
  have hc := (h3 0 0 (mu + mu') (yy_zero h1 h3 h4)).1 h0
  refine (h3 (-a) mu' (-mu) h').2 fun v => ?_
  obtain ⟨w, hw⟩ := hc v
  simp only [Pi.add_apply, Pi.zero_apply, zero_add] at hw
  refine ⟨-w, ?_⟩
  simp only [Pi.neg_apply, smul_neg]
  rw [← hw]
  abel

theorem yy_sub (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a b : G} {mu nu : Fin 8 → X} (ha : Y a mu)
    (hb : Y b nu) : Y (a - b) (mu - nu) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h4 _ _ _ _ ha (yy_neg h1 h3 h4 hb)

theorem yy_nsmul (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (k : ℕ) {a : G} {mu : Fin 8 → X} (ha : Y a mu) :
    Y (k • a) (k • mu) := by
  induction k with
  | zero => simpa using yy_zero h1 h3 h4
  | succ k ih => rw [succ_nsmul, succ_nsmul]; exact h4 _ _ _ _ ih ha

theorem mem_closure_iff (p J : ℕ) (hJ : 2 ≤ J) (hN : N = p ^ J) (hG : ∀ a : G, N • a = 0)
    (htor : ∀ b : G, p • b = 0 → ∃ c, b = p ^ (J - 1) • c) (htf : ∀ x : X, p ^ (J - 1) • x = 0 → x = 0)
    (h1 : ∀ a, ∃ mu, Y a mu) (h2 : ∀ mu, ∃ a, Y a mu)
    (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (S : Set G) (hS : ∀ a ∈ S, Y a 0)
    (hT : ∀ a, Y a 0 → ∃ b, p • b = 0 ∧ a + b ∈ S) (a : G) : a ∈ AddSubgroup.closure S ↔ Y a 0 := by
  constructor
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem x hx => exact hS x hx
    | zero => exact yy_zero h1 h3 h4
    | add x y _ _ hx hy => simpa using h4 x y 0 0 hx hy
    | neg x _ hx => simpa using yy_neg h1 h3 h4 hx
  · intro ha
    obtain ⟨b, hb, hab⟩ := hT a ha
    have hYb : Y b 0 := by simpa using yy_sub h1 h3 h4 (hS _ hab) ha
    obtain ⟨c, rfl⟩ := htor b hb
    obtain ⟨muc, hc⟩ := h1 c
    have hcong := (h3 _ _ _ (yy_nsmul h1 h3 h4 (p ^ (J - 1)) hc)).1 hYb
    have hw : ∀ v, ∃ w : X, muc v = p • w := by
      intro v
      obtain ⟨w, hw⟩ := hcong v
      simp only [Pi.zero_apply, Pi.smul_apply] at hw
      refine ⟨-w, ?_⟩
      have e : p ^ (J - 1) • (muc v + p • w) = 0 := by
        rw [smul_add, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN]
        exact hw.symm
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      exact htf _ e
    choose w hw using hw
    have hmu : muc = p • w := funext fun v => by simp [hw v]
    obtain ⟨c', hc'⟩ := h2 w
    have hk : Y (c - p • c') 0 := by
      have := yy_sub h1 h3 h4 hc (yy_nsmul h1 h3 h4 p hc')
      rwa [← hmu, sub_self] at this
    obtain ⟨bk, hbk, hkS⟩ := hT _ hk
    have hbk0 : p ^ (J - 1) • bk = 0 := by
      obtain ⟨e, he⟩ : ∃ e, J - 1 = e + 1 := ⟨J - 2, by omega⟩
      rw [he, pow_succ, mul_smul, hbk, smul_zero]
    have key : p ^ (J - 1) • c = p ^ (J - 1) • ((c - p • c') + bk) := by
      rw [smul_add, hbk0, add_zero, smul_sub, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN, hG, sub_zero]
    have hbcl : p ^ (J - 1) • c ∈ AddSubgroup.closure S := by
      rw [key]; exact nsmul_mem (AddSubgroup.subset_closure hkS) _
    have e : a = (a + p ^ (J - 1) • c) - p ^ (J - 1) • c := by abel
    rw [e]
    exact sub_mem (AddSubgroup.subset_closure hab) hbcl

theorem zmod_tors {p J M : ℕ} (hp : 0 < p) (hJ : 1 ≤ J) (hM : M = p ^ J) (x : ZMod M) (hx : p • x = 0) :
    ∃ y : ZMod M, x = p ^ (J - 1) • y := by
  subst hM
  haveI : NeZero (p ^ J) := ⟨pow_ne_zero _ hp.ne'⟩
  have h1 : p ^ J ∣ p * x.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (p ^ J)) (p ^ J)]
    push_cast
    rw [ZMod.natCast_zmod_val]
    rwa [nsmul_eq_mul] at hx
  have h2 : p ^ (J - 1) ∣ x.val := by
    have e : p ^ J = p * p ^ (J - 1) := by rw [← pow_succ']; congr 1; omega
    have h1' : p * p ^ (J - 1) ∣ p * x.val := by rw [← e]; exact h1
    exact Nat.dvd_of_mul_dvd_mul_left hp h1'
  obtain ⟨q, hq⟩ := h2
  refine ⟨(q : ZMod (p ^ J)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [hq, nsmul_eq_mul]
  push_cast
  ring

end
end GlobalTheory.Poinc.Sep.IntLabel

namespace GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Sep.IntLabel in

theorem mem_HH_iff_yy_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ ↔ 𝔪.YY a 0 := by
  intro g n F W Z i X₁ z₁ act x₀ hx₀ V _ _ _ ev X _ m t δ 𝔪 a
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  obtain ⟨j, hj, hr⟩ := X₁.ρ.r_eq
  have hp : 0 < X₁.ρ.n := X₁.ρ.n_prime.pos
  have hk := X₁.ρ.two_le
  have hN : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j + X₁.ρ.k * 2) := by rw [hr, X₁.ρ.N_eq, pow_add, pow_mul]
  have hJ : 2 ≤ j + X₁.ρ.k * 2 := by omega
  have hG : ∀ b : X₁.S.Gam, (X₁.S.r * X₁.S.N) • b = 0 := fun b => by
    funext v
    simp [nsmul_eq_mul]
  have htor : ∀ b : X₁.S.Gam, X₁.ρ.n • b = 0 → ∃ c : X₁.S.Gam, b = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • c := by
    intro b hb
    have hv : ∀ v, ∃ y : ZMod (X₁.S.r * X₁.S.N), b v = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • y := fun v =>
      zmod_tors hp (by omega) hN (b v) (by simpa using congrFun hb v)
    choose c hc using hv
    exact ⟨c, funext fun v => by simpa using hc v⟩
  have htf : ∀ x : X, X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • x = 0 → x = 0 := by
    intro x hx
    have hq : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) ≠ 0 := pow_ne_zero _ hp.ne'
    have hs : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • (Pi.single 0 x : Fin 8 → X) = 0 := by
      funext v
      by_cases hv : v = 0
      · subst hv; simp [hx]
      · simp [Pi.single_apply, hv]
    have he : ((X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) : ℕ) : ℤ) • 𝔪.e₈ (Pi.single 0 x) = 0 := by
      rw [natCast_zsmul, ← map_nsmul, hs, map_zero]
    have h0 : 𝔪.e₈ (Pi.single 0 x) = 0 := (smul_eq_zero.1 he).resolve_left (by exact_mod_cast hq)
    have h0' : (Pi.single 0 x : Fin 8 → X) = 0 := 𝔪.e₈.injective (h0.trans (map_zero _).symm)
    simpa using congrFun h0' 0
  rw [ThetaSys.HH]
  exact mem_closure_iff (X₁.ρ.n) (j + X₁.ρ.k * 2) hJ hN hG htor htf h1 h2 h3 h4 _
    (fun b hb => GlobalTheory.T.thetaLabel_class_zero_of_divides_all_thetaConstants g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 b hb)
    (fun b hb => GlobalTheory.T.exists_torsionTranslate_label_thetaConstant_divides_all g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hx₀ b hb) a

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeSlopeLowerBoundDefiniteCaseStatement
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenlattice_slope_lower_bound_definite_case : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : Type) [Group G] [Finite G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Finite (Comp Xo c) → Nonempty (Comp Xo c) → (∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom) → ActLev (Xo := Xo) c lev → FreePt Xo c lev → Dom a n → GoodW U ξ V dict (wtZ a n) → FlatExistsAt U ξ c₁ → eigLat U lev χ (wtZ a n) ≠ ⊥ ∧ defBound Dw a n c₁ ≤ slope_sq (normW U ξ V dict (wtZ a n)) (eigLat U lev χ (wtZ a n)) / 2 := by
  first | exact @GlobalTheory.DefPt.eigLat_slope_definite | exact GlobalTheory.DefPt.eigLat_slope_definite | (intros; apply GlobalTheory.DefPt.eigLat_slope_definite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.EighthTorsion
open MonObj

def precomp {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (x : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) where
  toFun g := x ≫ g
  map_one' := by simp
  map_mul' a b := by simp [MonObj.comp_mul]

def postcomp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    (T ⟶ G) →* (T ⟶ H) where
  toFun g := g ≫ f
  map_one' := by simp
  map_mul' a b := by simp [MonObj.mul_comp]

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (l : List (T ⟶ G)) : l.prod ≫ f = (l.map (· ≫ f)).prod :=
  (map_list_prod (postcomp (T := T) f) l)

theorem zpow_comp' {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (g : T ⟶ G) (n : ℤ) : (g ^ n) ≫ f = (g ≫ f) ^ n :=
  map_zpow (postcomp (T := T) f) g n

theorem ident_pow {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε)
    (A8 : PolAV (Sp (FractionRing T.V))) (pA : IsPowPolAV A8 T.A 8) :
    ∃ φ : P.A ≅ A8.A, IsMonHom φ.hom ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ φ.hom ≫ pA.pr a = ((List.finRange 8).map fun b => (φ.hom ≫ pA.pr b) ^ E a b).prod := by
  obtain ⟨c, ⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, pr, hpr, huniv, hL, hε⟩ := hD
  obtain ⟨e, he, hee⟩ := grpPullback_iso hc T.cart
  let p : IsPowGrp P.A T.A.A 8 :=
    { pr := fun a => pr a ≫ e.hom
      hom := fun a => by have := hpr a; infer_instance
      lim := Fan.IsLimit.mk _ (fun s => (huniv s.pt fun a => s.proj a ≫ e.inv).choose)
        (fun s a => by
          have h := (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.1 a
          change _ ≫ pr a ≫ e.hom = _
          rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
        (fun s m hm => (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.2 m fun a => by
          have h : m ≫ pr a ≫ e.hom = s.proj a := hm a
          rw [← h, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]) }
  obtain ⟨φ, hφ, hφp⟩ := GlobalTheory.PowerExamples.pow_unique p pA.toIsPowGrp
  have hφp' : ∀ a, φ.hom ≫ pA.pr a = pr a ≫ e.hom := hφp
  refine ⟨φ, hφ, ?_, ?_⟩
  · have hpt : ∀ a, (pr a).left ≫ φc = (φ.hom ≫ pA.pr a).left ≫ T.α := fun a => by
      rw [hφp' a, Over.comp_left, Category.assoc, hee]
    have hΛ : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb T.A.isLB _ _
    obtain ⟨w', hw'⟩ := T.lb
    have i₁ := iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
      (fun ab => W ab.1 ab.2)
    have i₂ := iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8)
      (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)
    have hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) =
        fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left ≫ T.α₂ :=
      funext fun ab => GlobalTheory.Poinc.SharpIdent.lift_comp_square hsq T.sq _ _ _ _ (hpt ab.1) (hpt ab.2)
    rw [hm] at i₁
    exact LBIso.trans P.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL
      (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)
  · intro E a
    haveI := he
    rw [hφp' a, ← Category.assoc, hε E a, prod_comp, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, hφp' b]
    exact zpow_comp' e.hom (pr b) (E a b)

theorem exists_proj {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε) :
    ∃ pr : Fin 8 → (P.A ⟶ T.A.A), (∀ a, IsMonHom (pr a)) ∧
      (∀ (T' : Over (Sp (FractionRing T.V))) (y : Fin 8 → (T' ⟶ T.A.A)), ∃! z : T' ⟶ P.A, ∀ a, z ≫ pr a = y a) ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ pr a = (List.ofFn fun b => pr b ^ E a b).prod := by
  obtain ⟨A8, pA, -⟩ := GlobalTheory.exists_powPolAV _ T.A 8
  obtain ⟨φ, hφ, hL, hε⟩ := ident_pow F W T P ε hD A8 pA
  refine ⟨fun a => φ.hom ≫ pA.pr a, fun a => by have := pA.hom a; infer_instance, fun T' y => ?_, hL,
    fun E a => by rw [List.ofFn_eq_map]; exact hε E a⟩
  refine ⟨pA.lim.lift (Fan.mk T' y) ≫ φ.inv, fun a => ?_, fun z hz => ?_⟩
  · rw [Category.assoc, φ.inv_hom_id_assoc]
    exact pA.lim.fac (Fan.mk T' y) ⟨a⟩
  · rw [Iso.eq_comp_inv]
    exact pA.lim.uniq (Fan.mk T' y) _ fun a => (Category.assoc _ _ _).trans (hz a.as)

theorem tau_coord {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (a b' : T.D.toPre.X)
    (x : (FractionRing T.V)ˣ) (hx : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord T.D.toPre a b' x) :
    ∃ u : T.Vˣ, (x : FractionRing T.V) =
      algebraMap T.V (FractionRing T.V) (u : T.V) * algebraMap T.V (FractionRing T.V) T.ϖ ^ (T.β a b') := by
  obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre (a + b')
  obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre a
  obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre b'
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.TauCoordQuot.main T.V T.D.toPre a b' x x₁ x₂ x₃ hx h₁ h₂ h₃
  obtain ⟨r₁, c₁, e₁⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₁
  obtain ⟨r₂, c₂, e₂⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₂
  obtain ⟨r₃, c₃, e₃⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₃
  obtain ⟨u, hu⟩ := T.mono.tau (fun i y z => by fin_cases i; exact T.symm y z)
    (Fin.forall_fin_one.2 T.irr.ne_zero) c₂ c₃ c₁
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hu
  refine ⟨u₀ * u, ?_⟩
  have key : algebraMap T.V (FractionRing T.V) (u₀ : T.V) * algebraMap T.V (FractionRing T.V) r₁ *
      (algebraMap T.V (FractionRing T.V) r₂)⁻¹ * (algebraMap T.V (FractionRing T.V) r₃)⁻¹ =
      algebraMap T.V (FractionRing T.V) (u₀ : T.V) * (algebraMap T.V (FractionRing T.V) r₁ /
        (algebraMap T.V (FractionRing T.V) r₂ * algebraMap T.V (FractionRing T.V) r₃)) := by
    rw [div_eq_mul_inv, mul_inv]; ring
  rw [hu₀, e₁, e₂, e₃, key, hu]
  simp only [Units.val_mul, map_mul]
  ring

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW T P ε hD
  have hCN : GlobalTheory.TorRef.IsCN T.V := ⟨inferInstance, inferInstance, T.complete, T.char⟩
  have hB : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, T.char⟩
  have hS : SharpOver F W P T.y := by
    obtain ⟨c, hc, pr, h₁, h₂, h₃, -⟩ := hD
    exact ⟨c, hc, pr, h₁, h₂, h₃⟩
  haveI : IsCommMonObj (powObj T.G 8) := GlobalTheory.PowerExamples.comm_of_pow (powIsPowGrp T.G 8)
  have hG' : IsSemiAbelian (powObj T.G 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ T.G 8 (powIsPowGrp T.G 8) T.semi
  obtain ⟨D', ⟨U'⟩⟩ := GlobalTheory.PowE8.exists_unif_pow8 g n _ _ F W hW T.V hCN T.D T.G T.A T.U T.y T.α T.α₂ T.semi T.cart
    T.sq T.lb P hS
  obtain ⟨pr, hpr, huniv, hL, hε⟩ := exists_proj F W T P ε hD
  obtain ⟨pG, c, e, hpG, hgen, hc, he⟩ := GlobalTheory.T.eighthPower_projections_extend_uniformisedGroups T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr
    huniv hL
  have hnn : ∀ a, 0 ≤ T.β a a := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · exact (GlobalTheory.Poinc.Trait.beta_pos g n _ _ F T a ha).le
  refine ⟨powObj T.G 8, inferInstance, inferInstance, hG', D', U', e, fun y => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff _ y).2 (GlobalTheory.PeriodFormCompare.psiIn_top D' y)
    obtain ⟨-, h⟩ := GlobalTheory.T.eighthPower_psiOrders_projectionLatticeCoordinates T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc
      e he T.ϖ T.β T.symm hnn (tau_coord T) y r hr
    obtain ⟨v, hv⟩ := h.symm
    exact ⟨v, by rw [mul_comm, hv]; exact hr⟩
  · rintro K _ _ _ m pk pk' x x' E hm h h' rfl
    exact GlobalTheory.T.matrix_acts_on_torsion_labels_alt T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc e he E (ε E)
      (hε E) K m pk pk' x hm h h'

end GlobalTheory.EighthTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicFactorOfUnimodularTensorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraic_factor_of_unimodular_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, 1 ≤ r → (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  first | exact @GlobalTheory.Mum.Tens.nonempty_factor | exact GlobalTheory.Mum.Tens.nonempty_factor | (intros; apply GlobalTheory.Mum.Tens.nonempty_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowSectionNonvanishingOnClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_pow_section_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ T : Set X, IsClosed T → (∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, T ⊆ NV P e 0 f := by
  intro k _ X _ p D hX P hA T hT hfin
  let Z : Closeds X := ⟨T, hT⟩
  obtain ⟨hAff, hFin⟩ := GlobalTheory.T.closedSubset_finiteFibres_isAffine_finite_int k X p D hX Z hfin
  haveI := hAff
  haveI := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  let i := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  obtain ⟨n, s, hn, hs⟩ := GlobalTheory.T.exists_nowhereZero_section_lineBundle_pow_finite_int _ hFin (P.L.B.pull i) (LB.isLB_pull hA.isLB i)
  obtain ⟨N, u, hN, hu⟩ := GlobalTheory.T.exists_ample_power_lift_of_nonvanishing_on_closed k X p D hX P.L.B hA _ i n s hn hs
  obtain ⟨f, hf, hfu⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P N).1 u
  refine ⟨N, hN, f, hf, ?_⟩
  rw [hfu]
  intro x hx
  apply hu
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hx

end GlobalTheory.HSAmp
end

