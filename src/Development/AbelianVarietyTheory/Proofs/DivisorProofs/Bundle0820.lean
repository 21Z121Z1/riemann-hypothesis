import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0766

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTwelfth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.CouplingCosets

theorem finite_ncard_cosets {E : Type} [Field E] [NumberField E] {n : ℕ} (A₁ A₀ : Submodule (𝓞 E) (Sp E n)) (c : ℕ) (hc : 0 < c)
    (h : ∀ y ∈ A₁, c • y ∈ A₀) :
    {Y : Set (Sp E n) | ∃ y ∈ A₁, Y = {z | z - y ∈ A₀}}.Finite ∧
      {Y : Set (Sp E n) | ∃ y ∈ A₁, Y = {z | z - y ∈ A₀}}.ncard ≤ c ^ (Module.finrank ℚ E * n) := by
  haveI : Module.Finite ℚ (Sp E n) := Module.Finite.trans E (Sp E n)
  have hd : Module.finrank ℚ (Sp E n) = Module.finrank ℚ E * n := by
    rw [← Module.finrank_mul_finrank ℚ E (Sp E n)]
    simp
  obtain ⟨hf, hle⟩ := GlobalTheory.SemilocalClasses.finite_card_le A₁.subtype.toAddMonoidHom (Submodule.subtype_injective _)
    (A₀.comap A₁.subtype).mkQ.toAddMonoidHom (Submodule.mkQ_surjective _) c hc fun x =>
      (Submodule.Quotient.mk_eq_zero _).2 (h x x.2)
  rw [hd] at hle
  let φ : (A₁ ⧸ A₀.comap A₁.subtype) → Set (Sp E n) := fun q => {z | z - ((Quotient.out q : A₁) : Sp E n) ∈ A₀}
  have hsub : {Y : Set (Sp E n) | ∃ y ∈ A₁, Y = {z | z - y ∈ A₀}} ⊆ Set.range φ := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    have h1 : (Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk (p := A₀.comap A₁.subtype) ⟨y, hy⟩)) :
        A₁ ⧸ A₀.comap A₁.subtype) = Submodule.Quotient.mk ⟨y, hy⟩ := Quotient.out_eq _
    have h2 := (Submodule.Quotient.eq _).1 h1
    set w : A₁ := Quotient.out (Submodule.Quotient.mk (p := A₀.comap A₁.subtype) ⟨y, hy⟩) with hw
    have h3 : (w : Sp E n) - y ∈ A₀ := h2
    ext z
    show z - (w : Sp E n) ∈ A₀ ↔ z - y ∈ A₀
    constructor
    · intro hz
      simpa using A₀.add_mem hz h3
    · intro hz
      simpa using A₀.sub_mem hz h3
  refine ⟨(Set.finite_range φ).subset hsub, ((Set.ncard_le_ncard hsub (Set.finite_range φ)).trans ?_).trans hle⟩
  exact Finite.card_range_le φ

theorem finite_ncard_ybSet {X : Fields} {Pr : Primes X} (hPr : Pr.Ok)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg) (hmu : mu = 1)
    (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (L : Submodule (𝓞 X.E) (Sp X.E n)) :
    (ybSet sel mu cst L).Finite ∧ (ybSet sel mu cst L).ncard ≤ (Pr.g 0 * Pr.g 1) ^ (Module.finrank ℚ X.E * n) := by
  classical
  have hvG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := by
    intro P
    rcases Finset.mem_union.mp P.2 with h | h
    · exact h
    · have h0 : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
        rw [hmu]
        exact twistPrimes_trivialTuple_empty sel Sg
      rw [h0] at h
      simp at h
  refine finite_ncard_cosets _ _ _ (Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos) ?_
  intro y hy
  unfold locLat at hy ⊢
  rw [Submodule.mem_iInf] at hy ⊢
  intro P
  have h1 := hy P
  rw [Submodule.mem_comap] at h1 ⊢
  simp only [hvG P, if_true, zpow_neg, zpow_one, inv_inv, zpow_zero, inv_one, one_smul, LinearMap.restrictScalars_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] at h1 ⊢
  rcases Finset.mem_union.mp (hvG P) with h | h
  · have hq : Formalism.L2.Col.qOf P.1 = Pr.g 0 := hPr.vG_norm 0 _ h
    rw [hq] at h1
    rw [mul_nsmul]
    exact nsmul_mem h1 _
  · have hq : Formalism.L2.Col.qOf P.1 = Pr.g 1 := hPr.vG_norm 1 _ h
    rw [hq] at h1
    rw [mul_nsmul']
    exact nsmul_mem h1 _

theorem ncard_ybSet_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ n ≤ N.Nm, (((ybSet sel mu cst (Formalism.L2.Col.stdLat X.E n)).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsLattice X.E L → ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H n hn
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, hmu, -⟩ := H
  have hf : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm, ← Module.finrank_mul_finrank ℚ X.F X.E, hX.ok.rankE, ← hX.ok.card_Tau, mul_comm]
    rfl
  have key : ∀ L : Submodule (𝓞 X.E) (Sp X.E n), ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (2 * errUnit N (Pr.T u)) := by
    intro L
    have h1 := (finite_ncard_ybSet hPr sel mu hmu cst L).2
    rw [hf, hg 0, hg 1] at h1
    have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
    have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
    have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
    have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
    have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
    have he : 2 * N.R.f * n ≤ 2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) := by
      refine Nat.mul_le_mul_left _ (hn.trans ?_)
      have hm : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by have := N.R.two_le_m; omega)
      calc N.Nm ≤ N.Nm ^ 2 := Nat.le_self_pow two_ne_zero _
        _ ≤ N.R.m ^ 2 * N.Nm ^ 2 := Nat.le_mul_of_pos_left _ hm
    calc ((ybSet sel mu cst L).ncard : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (2 * N.R.f * n) := by exact_mod_cast h1
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * n) := pow_le_pow_left₀ (by linarith) ggT _
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
      _ = Real.exp (2 * errUnit N (Pr.T u)) := by
        rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
        unfold errUnit
        push_cast
        ring
  exact ⟨key _, fun L _ => key L⟩

end GlobalTheory.CouplingCosets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

namespace GlobalTheory.ColumnNormCompare

theorem numRec_eq_ofRecord : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) →
    GlobalTheory.ColumnNormCompare.numDatumOfParameters D L = ofRecord D L Del h0 := by
  intro D L Del h0 hD hE
  have hm : (D.R.m : ℝ) ≠ 0 := by
    have := D.R.two_le_m
    exact_mod_cast (show D.R.m ≠ 0 by omega)
  have h1 : ⌊D.s.Del⌋₊ = Del := by rw [hD]; exact Nat.floor_natCast Del
  have h2 : ⌈LevelStarExponents.h0 L⌉₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [hE]; field_simp
    rw [this]; exact Nat.ceil_natCast h0
  simp only [numDatumOfParameters, ofRecord, h1, h2]

end GlobalTheory.ColumnNormCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyCupAnticommStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commAlgFunctorCohomologyCup_anticomm : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (a b : GlobalTheory.CatCoh.H1 F), cup F a b = - cup F b a := by
  first | exact @GlobalTheory.AbCoh.cup_anticomm | exact GlobalTheory.AbCoh.cup_anticomm | (intros; apply GlobalTheory.AbCoh.cup_anticomm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_adjoint_eq_of_pullback_iso : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ α β : A ⟶ A, IsMonHom α → IsMonHom β → LBIso (P.pull (lift (fst A A ≫ α) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ β)).left) → ∀ (n : ℤ) (T : Over S) (a b : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift (a ≫ α) 1) (lift 1 b) c → Out.WeilIs (G2 A) P n (lift a 1) (lift 1 (b ≫ β)) c' → c = c' := by
  first | (exact @GlobalTheory.AdjPairing.weilIs_adj_eq) | (exact GlobalTheory.AdjPairing.weilIs_adj_eq) | (intros; apply GlobalTheory.AdjPairing.weilIs_adj_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_swap_eq_of_swap_invariant : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift 1 u) (lift v 1) c → Out.WeilIs (G2 A) P n (lift u 1) (lift 1 v) c' → c = c' := by
  first | (exact @GlobalTheory.SwapPairing.weilIs_swap_eq) | (exact GlobalTheory.SwapPairing.weilIs_swap_eq) | (intros; apply GlobalTheory.SwapPairing.weilIs_swap_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffPIterateInvariantDerivationCoordStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_pIterate_invariantDerivation_coord : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (l : MvPowerSeries (Fin d) Q) (j : Fin d), QL μ ⊤ l → In (RingHom.ker θ) (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ c : Fin d → B, (∀ i, algebraMap B Q (c i) = (p : Q) * coeff (Finsupp.single i p) l) → ∀ u : Fin d → B, constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p ∈ RingHom.ker θ ⊔ Ideal.span {(p : B)} := by
  first | exact @GlobalTheory.FrobIter.constantCoeff_iterate_invDer_X_sub_mem | exact GlobalTheory.FrobIter.constantCoeff_iterate_invDer_X_sub_mem | (intros; apply GlobalTheory.FrobIter.constantCoeff_iterate_invDer_X_sub_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContConeOfQcqsAffineStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_of_qcqs_affine
  | exact GlobalTheory.EtC.contCone_of_qcqs_affine
  | (intros; apply GlobalTheory.EtC.contCone_of_qcqs_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoupledClassSumCauchySchwarzStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coupled_class_sum_cauchy_schwarz : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (v : InfinitePlace K) (t₁ t₂ h₀ h h₁ ny : ℝ), 0 ≤ t₁ → 0 ≤ t₂ → 0 ≤ h₀ → 0 ≤ h → 0 ≤ h₁ → 0 ≤ ny → (∀ b, PosAt ((Q.F Q.n).mem b) v) → PosAt Q.S v → PosAt Q.S₁ v → (∀ b, (Nat.card ((Q.F Q.n).mem b).Cl : ℝ) ≤ h₀) → (Nat.card Q.S.Cl : ℝ) ≤ h → (Nat.card Q.S₁.Cl : ℝ) ≤ h₁ → (∀ d, ((Q.Y.ys d).ncard : ℝ) ≤ ny) → (∀ b d₀ d, ∀ y ∈ Q.Y.ys d, OpLe ((Q.F Q.n).mem b) Q.S v ((Q.cp b).k1 d₀ d y) t₁) → (∀ b d d₁, ∀ y ∈ Q.Y.ys d, OpLe Q.S Q.S₁ v ((Q.cp b).k2 d y d₁) t₂) → ∀ φ : (Q.F Q.n).Forms, (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤ (Fintype.card (Q.F Q.n).β : ℝ) * h₀ * h ^ 2 * h₁ * ny ^ 2 * t₁ * t₂ * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
  first | exact @GlobalTheory.ColNorms.CplCS.cpl_le | exact GlobalTheory.ColNorms.CplCS.cpl_le | (intros; apply GlobalTheory.ColNorms.CplCS.cpl_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartanStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverUpq_closure_exp_top_and_cartan : ∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q, Subgroup.closure (T.expt '' upq p q) = ⊤ ∧ ∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  first | exact @GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan | exact GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan | (intros; apply GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOnEqZeroOfEqOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory

open TopForm

namespace TopForm

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} {U : Y.Opens}

theorem dOn_eq_zero_of_eq_one (f : Fin D → Γ(Y, U)) (b : Fin D) (hb : f b = 1) : dOn p f = 0 := by
  rw [dOn, dForm_eq]
  refine AlternatingMap.map_coord_zero _ b ?_
  let := (algX p U).toAlgebra
  rw [hb]
  exact (KaehlerDifferential.D k Γ(Y, U)).map_one_eq_zero

theorem jacOn_of_eq_one (f : Fin (D + 1) → Γ(Y, U)) (i : Fin (D + 1)) (hi : f i = 1) :
    jacOn p f = (-1 : Γ(Y, U)) ^ (i : ℕ) • dOn p fun b => f (i.succAbove b) := by
  rw [jacOn_eq, Finset.sum_eq_single i, hi, mul_one]
  · intro a _ ha
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (Ne.symm ha)
    rw [dOn_eq_zero_of_eq_one _ b (by rw [hb, hi]), smul_zero]
  · simp

theorem isUnit_of_affine {f : Γ(Y, U)}
    (h : ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ U, IsUnit (resG Y hW f)) : IsUnit f := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => ?_
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hx
  have := (h W hW hWU).map (Y.presheaf.germ W x hxW).hom
  rwa [show (Y.presheaf.germ W x hxW).hom (resG Y hWU f) = (Y.presheaf.germ U x hx).hom f from
    Y.presheaf.germ_res_apply (homOfLE hWU) x hxW f] at this

theorem isFreeGen_dForm_X (k : Type) [CommRing k] (D : ℕ) : IsFreeGen (MvPolynomial (Fin D) k)
    (dForm (algebraMap k (MvPolynomial (Fin D) k)) (X : Fin D → _)) := by
  have key (inst : Algebra k (MvPolynomial (Fin D) k))
      (e : inst = AddMonoidAlgebra.algebra) :
      IsFreeGen (MvPolynomial (Fin D) k) (@dWedge k _ _ _ inst D X) := by
    subst e
    have := isFreeGen_ιMulti (KaehlerDifferential.mvPolynomialBasis k (Fin D))
    rwa [funext (KaehlerDifferential.mvPolynomialBasis_apply k (Fin D))] at this
  exact key _ (Algebra.algebra_ext _ _ fun _ => rfl)

end TopForm

namespace ProjSpace

variable (R : Type) [CommRing R] (N : ℕ)

theorem isFrame_dOn_ratio (i : Fin (N + 1)) :
    IsFrame (dOn (PSpace.str R N) fun b : Fin N => ratio R N i (i.succAbove b)) := by
  refine ⟨isAffineOpen_chart R N i, ?_⟩
  let e : MvPolynomial (Fin N) R ≃ₐ[R] Γ(PSpace R N, chart R N i) :=
    (renameEquiv R (finSuccAboveEquiv i)).trans (chartAlgEquiv R N i)
  have he : (e : MvPolynomial (Fin N) R →+* _).comp (algebraMap R _) =
      algX (PSpace.str R N) (chart R N i) := RingHom.ext fun r => e.commutes r
  have := (isFreeGen_dForm_X R N).formMap (RingHom.Etale.of_bijective e.bijective) he
  rw [formMap_dForm] at this
  convert this using 3 with b
  exact ((congrArg (chartAlgEquiv R N i) (rename_X _ b)).trans
    (chartAlgEquiv_X R N i (finSuccAboveEquiv i b))).symm

theorem isUnit_jacSec_coord [SmoothOfRelativeDimension N (PSpace.str R N)]
    (K : CanonLB (PSpace.str R N) N) (c : (K.adj (O1 R N) (N + 1)).ι) :
    IsUnit ((K.jacSec (coord R N)).f c) := by
  refine isUnit_of_affine fun W hW h => ?_
  have l := h.trans (K.adj_U_le _ c)
  have h₂ : W ≤ chart R N (c.2 PUnit.unit) := l.trans inf_le_right
  rw [K.resG_jacSec_f _ c h (l.trans inf_le_left) h₂]
  change IsUnit (K.coeff _ _ (jacOn _ (ratioOn W (c.2 PUnit.unit) h₂)))
  rw [jacOn_of_eq_one _ (c.2 PUnit.unit) (ratioOn_self (hi := h₂)), map_smul, smul_eq_mul]
  refine (isUnit_one.neg.pow _).mul ((K.isUnit_jacobian_iff _ hW _ _).2 ?_)
  have := (isFrame_dOn_ratio R N (c.2 PUnit.unit)).res hW h₂
  rw [resForm_dOn] at this
  exact this

end ProjSpace

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefectCompat
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem isLift_id_of_isLaw {O : Type} [CommRing O] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (h : IsLaw μ) : IsLift (RingHom.id O) μ where
  const := h.const
  unit := h.unit
  comm := h.comm
  law := by simpa using h

theorem defect_compat : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → (∀ n, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0) ∧ ∀ (n : ℕ) (s s' : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → map (algebraMap O E) s' = defect c.μ (p ^ (n + 1)) f → ∃ z, c.ev (n + 1) s' = G.mulP n (c.ev n s) + (p : O) ^ n • z := by
  intro p _ O E _ _ _ hF G d c f hf
  have hD := QLogDefect.main p O O E (RingHom.id O) hF d c.μ (isLift_id_of_isLaw c.isLaw) ⊤ f hf
  have hex : ∀ n, ∃ s : MvPowerSeries (Fin d) O,
      map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0 := fun n => by
    obtain ⟨s, -, hs⟩ := (T.coeffsInIdealOfPowerSeries_iff_image O E (Fin d) ⊤ _).1.1 (hD n).1
    refine ⟨s, hs, hF.inj ?_⟩
    have h0 : ∀ i, constantCoeff (up E (nmul c.μ n) i) = 0 := fun i => by
      simp [up, (hD n).2 i]
    rw [← constantCoeff_map, hs, map_zero, defect, map_sub,
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf.1]
    simp [hf.1]
  refine ⟨hex, fun n s s' hs hs' => ?_⟩
  obtain ⟨κ, -, hκ⟩ := (T.coeffsInIdealOfPowerSeries_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1.1 hf.2.2
  obtain ⟨s₁, hs₁, -⟩ := hex p
  have h := ((T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ).2.2 p s₁ hs₁).2 (p ^ n) s s' hs
    (by rw [← pow_succ]; exact hs')
  haveI := hF.complete
  refine ⟨c.ev (n + 1) s₁, ?_⟩
  rw [h, map_add, map_smul, (T.ev_subst_natMultiple_prime_pow_constant p O G d c n).2.2, Nat.cast_pow]
  exact add_comm _ _

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAtZeroReindexEqTaylorCoefficientStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivAtZero_reindex_eq_taylor_coefficient : ∀ (D : D7) (ι : Type) [Fintype ι] (e : ι ≃ D.what₂.Tau) (a b : ℕ) (F : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ F → ∀ m : DVar ι a b →₀ ℕ, derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D F (Finsupp.equivMapDomain (e.prodCongr (Equiv.refl (Fin b × Fin a))) m) := by
  first | exact @GlobalTheory.DerivReindex.derivAt0_reindex | exact GlobalTheory.DerivReindex.derivAt0_reindex | (intros; apply GlobalTheory.DerivReindex.derivAt0_reindex <;> assumption)
end

