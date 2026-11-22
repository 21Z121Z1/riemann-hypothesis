import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyCupAnticomm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem cup_anticomm (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (a b : GlobalTheory.CatCoh.H1 F) : cup F a b = - cup F b a := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨a, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add]
  refine GlobalTheory.CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * b.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp a, Z1.comp b, map_mul, map_neg]
  ring

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.AdjPairing

theorem weilIs_adj_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ α β : A ⟶ A, IsMonHom α → IsMonHom β → LBIso (P.pull (lift (fst A A ≫ α) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ β)).left) → ∀ (n : ℤ) (T : Over S) (a b : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift (a ≫ α) 1) (lift 1 b) c → Out.WeilIs (G2 A) P n (lift a 1) (lift 1 (b ≫ β)) c' → c = c' := by
  intro S A _ _ P hA hP α β hα hβ hiso n T a b c c' h h'
  let ψ₁ : G2 A ⟶ G2 A := lift (fst A A ≫ α) (snd A A)
  let ψ₂ : G2 A ⟶ G2 A := lift (fst A A) (snd A A ≫ β)
  haveI : IsMonHom ψ₁ := inferInstanceAs (IsMonHom (lift (fst A A ≫ α) (snd A A)))
  haveI : IsMonHom ψ₂ := inferInstanceAs (IsMonHom (lift (fst A A) (snd A A ≫ β)))
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hL : (P.pull ψ₁.left).IsLB := pull_isLB hP _
  have hx₁ : lift a 1 ≫ ψ₁ = lift (a ≫ α) 1 := by ext <;> simp [ψ₁]
  have hy₁ : lift 1 b ≫ ψ₁ = lift 1 b := by ext <;> simp [ψ₁]
  have hx₂ : lift a 1 ≫ ψ₂ = lift a 1 := by ext <;> simp [ψ₂]
  have hy₂ : lift 1 b ≫ ψ₂ = lift 1 (b ≫ β) := by ext <;> simp [ψ₂]
  have hw₁ : LBIso (lbPow (P.pull ψ₁.left) 1) (P.pull ψ₁.left) := lbIso_lbPow_one hL
  have hw₂ : LBIso (lbPow (P.pull ψ₁.left) 1) (P.pull ψ₂.left) :=
    LBIso.trans (isLB_lbPow hL 1) hL (pull_isLB hP _) (lbIso_lbPow_one hL) hiso
  have h1 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift a 1) (y := lift 1 b)
    globalFns_holds hAA hL hP ψ₁ hw₁ (by rw [hx₁, hy₁]; exact h)
  have h2 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift a 1) (y := lift 1 b)
    globalFns_holds hAA hL hP ψ₂ hw₂ (by rw [hx₂, hy₂]; exact h')
  rw [Nat.cast_one, _root_.mul_one] at h1 h2
  exact CommutatorPairing.weilIs_unique globalFns_holds hAA hL h1 h2

end GlobalTheory.AdjPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SwapPairing

theorem weilIs_swap_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift 1 u) (lift v 1) c → Out.WeilIs (G2 A) P n (lift u 1) (lift 1 v) c' → c = c' := by
  intro S A _ _ P hA hP hiso n T u v c c' h h'
  let ψ : G2 A ⟶ G2 A := lift (snd A A) (fst A A)
  haveI : IsMonHom ψ := inferInstanceAs (IsMonHom (lift (snd A A) (fst A A)))
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hx : lift u 1 ≫ ψ = lift 1 u := by ext <;> simp [ψ]
  have hy : lift 1 v ≫ ψ = lift v 1 := by ext <;> simp [ψ]
  have hw : LBIso (lbPow P 1) (P.pull ψ.left) :=
    LBIso.trans (isLB_lbPow hP 1) hP (pull_isLB hP _) (lbIso_lbPow_one hP) hiso
  have h1 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift u 1) (y := lift 1 v)
    globalFns_holds hAA hP hP ψ hw (by rw [hx, hy]; exact h)
  rw [Nat.cast_one, _root_.mul_one] at h1
  exact CommutatorPairing.weilIs_unique globalFns_holds hAA hP h1 h'

end GlobalTheory.SwapPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffPIterateInvariantDerivationCoord
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.FrobIter

def iterLin {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (u : Fin d → R) (n : ℕ) :
    MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R where
  toFun := (invDer μ u)^[n]
  map_add' := by
    obtain ⟨hadd, -, -⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hμ u
    induction n with
    | zero => intro F G; rfl
    | succ n ih => intro F G; simp only [Function.iterate_succ_apply', ih, hadd]
  map_smul' := by
    obtain ⟨-, hsmul, -⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hμ u
    induction n with
    | zero => intro a F; rfl
    | succ n ih => intro a F; simp only [Function.iterate_succ_apply', ih, hsmul, RingHom.id_apply]

theorem iterLin_apply {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (u : Fin d → R) (n : ℕ) (F : MvPowerSeries (Fin d) R) :
    iterLin hμ u n F = (invDer μ u)^[n] F := rfl

theorem constantCoeff_iterate_invDer_X_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (l : MvPowerSeries (Fin d) Q) (j : Fin d), QL μ ⊤ l → In (RingHom.ker θ) (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ c : Fin d → B, (∀ i, algebraMap B Q (c i) = (p : Q) * coeff (Finsupp.single i p) l) → ∀ u : Fin d → B, constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p ∈ RingHom.ker θ ⊔ Ideal.span {(p : B)} := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL l j hQL hcob hlin c hc u
  classical
  have hp : p.Prime := Fact.out
  have hμ := hL.const
  have hμQ : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ,
      map_zero]
  obtain ⟨b, hbN, hb⟩ := GlobalTheory.T.constantCoeff_iterate_invariantDerivation_mem B Q d μ hμ (RingHom.ker θ) l j hcob hlin u p hp.two_le
  have h3 := GlobalTheory.T.coeff_quasiLogarithm_integral_low_degree p B O Q θ hF d μ hL l hQL
  let P : (Fin d →₀ ℕ) → Prop := fun α => α.degree ≤ p ∧ ∀ i, α ≠ Finsupp.single i p
  let h : (Fin d →₀ ℕ) → B := fun α => if hα : P α then (h3 α hα.1 hα.2).choose else 0
  have hh : ∀ α, P α → algebraMap B Q (h α) = coeff α l := fun α hα => by
    simp only [h, dif_pos hα]; exact (h3 α hα.1 hα.2).choose_spec.symm
  let H : MvPowerSeries (Fin d) B := fun α => h α
  have hH : ∀ α, coeff α H = h α := fun α => rfl
  let q : Fin d → Q := fun i => coeff (Finsupp.single i p) l
  have hinj : ∀ i k : Fin d, Finsupp.single i p = Finsupp.single k p ↔ i = k := fun i k =>
    Finsupp.single_left_inj hp.ne_zero
  let G : MvPowerSeries (Fin d) Q :=
    map (algebraMap B Q) H + ∑ i, q i • monomial (Finsupp.single i p) (1 : Q)
  have hG : ∀ α : Fin d →₀ ℕ, α.degree ≤ p → coeff α l = coeff α G := by
    intro α hα
    simp only [G, map_add, coeff_map, hH, map_sum, map_smul, coeff_monomial, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    by_cases hP : ∀ i, α ≠ Finsupp.single i p
    · rw [hh α ⟨hα, hP⟩, Finset.sum_eq_zero (fun i _ => if_neg (hP i)), add_zero]
    · push_neg at hP
      obtain ⟨i, rfl⟩ := hP
      have : h (Finsupp.single i p) = 0 := dif_neg fun hα => hα.2 i rfl
      rw [this, map_zero, zero_add, Finset.sum_eq_single i (fun k _ hk => if_neg fun e =>
        hk ((hinj i k).1 e).symm) (by simp), if_pos rfl]

  have hnat : ∀ F : MvPowerSeries (Fin d) B,
      constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[p] (map (algebraMap B Q) F)) =
        algebraMap B Q (constantCoeff ((invDer μ u)^[p] F)) := fun F => by
    rw [← constantCoeff_map, GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate B Q (algebraMap B Q) d μ hμ u p F]; rfl
  have hmon : ∀ i : Fin d, monomial (Finsupp.single i p) (1 : Q) =
      map (algebraMap B Q) (monomial (Finsupp.single i p) (1 : B)) := fun i => by
    rw [map_monomial, (algebraMap B Q).map_one]
  have hmono : ∀ i : Fin d, constantCoeff ((invDer μ u)^[p] (monomial (Finsupp.single i p) (1 : B))) =
      (p.factorial : B) * u i ^ p := fun i => by
    have := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_monomial B d μ hμ hL.unit hL.comm u (Finsupp.single i p)
    rw [Finsupp.degree_single] at this
    rw [this, Finset.prod_eq_single i (fun k _ hk => by rw [Finsupp.single_apply, if_neg (Ne.symm hk),
      pow_zero]) (by simp), Finsupp.single_eq_same]
  have e1 := GlobalTheory.T.constantCoeff_iterate_invariantDerivation_congr Q d (up Q μ) hμQ (fun i => algebraMap B Q (u i)) p l G hG
  have e2 : constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[p] G) =
      algebraMap B Q (constantCoeff ((invDer μ u)^[p] H)) +
        ∑ i, q i * algebraMap B Q ((p.factorial : B) * u i ^ p) := by
    rw [← iterLin_apply hμQ]
    simp only [G, map_add, map_sum, map_smul, iterLin_apply, hmon, hnat]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul, map_mul, constantCoeff_C, hnat, hmono]
  obtain ⟨r, hr⟩ := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_linear p B d μ hμ hL.unit hL.comm u H
  have hlin1 : ∀ k, coeff (Finsupp.single k 1) H = if k = j then 1 else 0 := fun k => by
    apply hF.inj
    have hPk : P (Finsupp.single k 1) := ⟨by rw [Finsupp.degree_single]; exact hp.one_le, fun i e => by
      rcases (Finsupp.single_eq_single_iff _ _ _ _).1 e with ⟨_, h1⟩ | ⟨h1, _⟩
      · exact hp.one_lt.ne h1
      · exact one_ne_zero h1⟩
    rw [hH, hh _ hPk]
    have := congrFun hlin k
    simp only [lin] at this
    rw [this, Pi.single_apply]
    split_ifs <;> simp
  have hsumX : ∑ k, constantCoeff ((invDer μ u)^[p] (X k)) * coeff (Finsupp.single k 1) H =
      constantCoeff ((invDer μ u)^[p] (X j)) := by
    simp [hlin1]
  rw [hsumX] at hr
  have key : b = constantCoeff ((invDer μ u)^[p] H) + ((p - 1).factorial : B) * ∑ i, c i * u i ^ p := by
    apply hF.inj
    rw [← hb, e1, e2]
    simp only [map_add, map_mul, map_sum, map_pow, map_natCast]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc, ← Nat.mul_factorial_pred hp.ne_zero]
    push_cast
    ring
  obtain ⟨m, hm⟩ : p ∣ (p - 1).factorial + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  have hmB : ((p - 1).factorial : B) = p * m - 1 := by
    have := congrArg (Nat.cast : ℕ → B) hm
    push_cast at this
    linear_combination this
  have eq : constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p =
      b - p * (r + m * ∑ i, c i * u i ^ p) := by
    rw [key, hmB]
    linear_combination -hr
  rw [eq]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hbN)
    (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 ⟨_, rfl⟩))

end GlobalTheory.FrobIter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContConeOfQcqsAffine
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_qcqs_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hcp hqs haff
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hc' : IsLimit ((Over.conePost G i₀).obj c) := Over.isLimitConePost i₀ hc
  haveI := hcp i₀
  haveI := hqs i₀
  have hcore := GlobalTheory.T.cohomologyContinuous_baseChange_qcqs R F hF (G.obj i₀) (Over i₀) (Over.post G) ((Over.conePost G i₀).obj c) hc'
    (fun j => haff _ _ j.hom) (G.obj i₀) (𝟙 _)
  have hb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  haveI : IsIso (sch.map (𝟙 (G.obj i₀))) := inferInstance
  apply GlobalTheory.T.cohomologyContinuousOnCone_of_whisker R F I (Over i₀) (Over.forget i₀) (G ⋙ sch) (sch.mapCone c)
  · intro i
    exact ⟨Over.mk (IsCofiltered.minToRight i i₀), ⟨IsCofiltered.minToLeft i i₀⟩⟩
  · let α : Over.post G ⋙ bc (sch.map (𝟙 (G.obj i₀))) ⟶ Over.forget i₀ ⋙ G ⋙ sch :=
      { app := fun j => pullback.snd _ _
        naturality := fun j k f => by
          simp only [Functor.comp_map, bc, pullback.map]
          erw [pullback.lift_snd]
          rfl }
    refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F (Over i₀) _ _ ((bc (sch.map (𝟙 (G.obj i₀)))).mapCone ((Over.conePost G i₀).obj c))
      ((sch.mapCone c).whisker (Over.forget i₀)) α (pullback.snd _ _) ?_ ?_ ?_).1 hcore
    · intro j
      simp only [Functor.mapCone_π_app, Cone.whisker_π, bc, pullback.map]
      erw [pullback.lift_snd]
      rfl
    · intro j
      exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
    · exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtLogNorm
section
open Filter Topology MeasureTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O
open ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Mean4O

namespace BdSec

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}

theorem levi_log_norm {G : (Fin e → ℂ) → ℂ} {z : Fin e → ℂ} (hG : AnalyticAt ℂ G z) (h0 : G z ≠ 0)
    (w : Fin e → ℂ) : levi (fun y => Real.log ‖G y‖) z w = 0 := by
  have h1 : AnalyticAt ℂ (fun y => Complex.log (G y / G z)) z :=
    (hG.div_const (c := G z)).clog (by simp [div_self h0])
  have h2 : (fun y => Real.log ‖G y‖ - Real.log ‖G z‖) =ᶠ[𝓝 z] fun y => (Complex.log (G y / G z)).re := by
    filter_upwards [hG.continuousAt.eventually_ne h0] with y hy
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hy) (norm_ne_zero_iff.2 h0)]
  rw [← levi_sub_const _ (Real.log ‖G z‖), levi_congr h2, levi_re_analytic h1]

theorem contDiffAt_log_norm {G : (Fin e → ℂ) → ℂ} {z : Fin e → ℂ} (hG : AnalyticAt ℂ G z) (h0 : G z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log ‖G y‖) z :=
  (((hG.restrictScalars (𝕜 := ℝ)).contDiffAt).norm ℝ h0).log (norm_ne_zero_iff.2 h0)

theorem contDiffAt_pot {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) y :=
  (hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy)

theorem mem_interior_iff (hS : IsSection A L s) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x) :
    (A.chart j).symm y ∈ interior (bdry s) ↔ ∀ᶠ z in 𝓝 y, s x ((A.chart j).symm z) = 0 := by
  rw [mem_interior_iff_mem_nhds, ← (A.chart j).symm.map_nhds_eq hy.1, mem_map]
  refine eventually_congr ?_
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm (L.isOpen_U x)).mem_nhds hy] with z hz
  exact bdry_iff hS hz.2

theorem interior_bdry [ConnectedSpace X] (hS : IsSection A L s) (h : bdry s ≠ Set.univ) :
    interior (bdry s) = ∅ := by
  have hc : IsClosed (interior (bdry s)) := by
    rw [← closure_subset_iff_isClosed]
    intro p hp
    obtain ⟨j, hj⟩ := A.cover p
    have hO := (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U p)
    have hpO : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p :=
      ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using L.mem_U p⟩
    obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hO _ hpO
    obtain ⟨q, ⟨hq, hqB⟩, hqi⟩ := mem_closure_iff.1 hp _
      ((A.chart j).isOpen_inter_preimage (Metric.isOpen_ball (x := A.chart j p) (ε := ε)))
      ⟨hj, Metric.mem_ball_self hε⟩
    rw [← (A.chart j).left_inv hq, mem_interior_iff hS p j (hB hqB)] at hqi
    have h1 := ((hS.1 p j).mono hB).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball _ _).isPreconnected hqB hqi
    rw [← (A.chart j).left_inv hj, mem_interior_iff hS p j hpO]
    filter_upwards [Metric.ball_mem_nhds _ hε] with z hz using h1 hz
  rcases isClopen_iff.1 ⟨hc, isOpen_interior⟩ with h1 | h1
  · exact h1
  · exact absurd (interior_eq_univ.1 h1) h

theorem bdry_null_chart (hS : IsSection A L s) (h : interior (bdry s) = ∅) (j : Fin A.n) :
    volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' bdry s) = 0 := by
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(bdry_iff hS hzU).2 (hz 0), hzU⟩
  have := analyticNull A (bdry s) hAn h j
  rwa [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this

theorem continuous_norm_sec (hL : IsPotential A L) (hS : IsSection A L s) :
    Continuous fun y => ‖s y y‖ * Real.exp (-L.φ y y) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc := continuousAt_of_holoOn A (hS.1 y) (L.mem_U y)
  have hφ := continuousAt_of_smoothOn A (L.isOpen_U y) (hL.1 y) (L.mem_U y)
  refine (hc.norm.mul (Real.continuous_exp.continuousAt.comp hφ.neg)).congr ?_
  filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
  exact hS.2 y z z ⟨hz, L.mem_U z⟩

variable {r : X → ℝ}

theorem toBot (hL : IsPotential A L) (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) :
    ToBot (bdry s) fun x => -r x := by
  intro a
  have hc := isClosed_le (continuous_const (y := Real.exp ((Real.exp 1 - a) / 2))) (continuous_norm_sec hL hS)
  refine (closure_minimal ?_ hc).trans ?_
  · rintro x ⟨hx, hxa⟩
    have hx' : s x x ≠ 0 := hx
    simp only [hr x hx, rW, logNormSec] at hxa
    exact (Real.le_log_iff_exp_le (mul_pos (norm_pos_iff.2 hx') (Real.exp_pos _))).1 (by linarith)
  · intro x hx hx0
    have hx' : s x x = 0 := hx0
    rw [Set.mem_setOf_eq, hx', norm_zero, zero_mul] at hx
    exact (Real.exp_pos _).not_ge hx

theorem local_eq (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) {x z : X} (hz : z ∈ L.U x)
    (h0 : s x z ≠ 0) : r z = Real.exp 1 - 2 * (Real.log ‖s x z‖ - L.φ x z) := by
  rw [hr z fun h => h0 ((bdry_iff hS hz).1 h), rW, logNormSecLocal A L s x z hS hz h0]

theorem local_eventuallyEq (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (h0 : (A.chart j).symm y ∉ bdry s) :
    ∀ᶠ z in 𝓝 y, r ((A.chart j).symm z) = Real.exp 1 - 2 *
      (Real.log ‖s ((A.chart j).symm y) ((A.chart j).symm z)‖ - L.φ ((A.chart j).symm y) ((A.chart j).symm z)) := by
  have hm : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y) := ⟨hy, L.mem_U _⟩
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm (L.isOpen_U _)).mem_nhds hm,
    (hS.1 _ j y hm).continuousAt.eventually_ne h0] with z hz hz0
  exact local_eq hS hr hz.2 hz0

theorem smoothOn (hL : IsPotential A L) (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) :
    A.SmoothOn (bdry s)ᶜ r := by
  intro j y hy
  have hm : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y) := ⟨hy.1, L.mem_U _⟩
  exact ((contDiffAt_const.sub (contDiffAt_const.mul ((contDiffAt_log_norm (hS.1 _ j y hm) hy.2).sub
    (contDiffAt_pot hL _ j hm)))).congr_of_eventuallyEq
    (local_eventuallyEq hS hr j hy.1 hy.2)).contDiffWithinAt

theorem mIntegrable (hL : IsPotential A L) (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x)
    (h : interior (bdry s) = ∅) {Φ : Fin e → LocPot X} (hΦ : ∀ i, IsPotential A (Φ i)) :
    MIntegrable A Φ (cut (bdry s) Set.univ r) := by
  intro j K hKt hK
  refine LocallyIntegrableOn.integrableOn_isCompact (fun y hy => ?_) hK
  set x := (A.chart j).symm y with hx
  have hO := (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U x)
  have hm : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x := ⟨hKt hy, L.mem_U _⟩
  obtain ⟨B, hBn, hB, hBc⟩ := local_compact_nhds (hO.mem_nhds hm)
  refine ⟨B, mem_nhdsWithin_of_mem_nhds hBn, ?_⟩
  obtain ⟨h1, h2⟩ := locallyIntegrableOn_log_norm_of_frequently_ne_zero volume hO (hS.1 x j).differentiableOn
    fun z hz hev => by
      have := (mem_interior_iff hS x j hz).2 (hev.mono fun _ h => not_not.1 h)
      rw [h] at this
      exact this
  have h3 := h2.integrableOn_compact_subset hB hBc
  have h4 : IntegrableOn (L.φ x ∘ (A.chart j).symm) B :=
    ((hL.1 x j).continuousOn.mono hB).integrableOn_compact hBc
  have h5 : IntegrableOn (fun _ => Real.exp 1) B := continuousOn_const.integrableOn_compact hBc
  have h6 : IntegrableOn (fun z => Real.exp 1 - 2 * (Real.log ‖s x ((A.chart j).symm z)‖ -
      L.φ x ((A.chart j).symm z))) B := h5.sub ((h3.sub h4).const_mul 2)
  refine (h6.mul_continuousOn ((locDensCont A Φ hΦ j).mono (hB.trans Set.inter_subset_left)) hBc).congr ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hB h1, ae_restrict_mem hBc.measurableSet] with z hz hzB
  have hzU := (hB hzB).2
  rw [cut, Set.indicator_of_mem (show _ ∈ Set.univ ∩ (bdry s)ᶜ from
    ⟨trivial, fun h => hz ((bdry_iff hS hzU).1 h)⟩), local_eq hS hr hzU hz]

theorem exists_pshOff [CompactSpace X] [T2Space X] {Om : LocPot X} (hO : IsPotential A Om) (hP : IsPosPot A Om)
    (hL : IsPotential A L) (hS : IsSection A L s) (hr : ∀ x, x ∉ bdry s → r x = rW L s x) :
    ∃ c : ℝ, 0 < c ∧ PshOff A (bdry s) (Om + LocPot.ofFun fun x => -c * r x) := by
  obtain ⟨C, hC, -, hpsh⟩ := TailBoundAlt.exists_psh_chern_bound A Om L hO hP hL
  refine ⟨1 / (2 * (C + 1)), by positivity, fun j y hy h0 w => ?_⟩
  set c := 1 / (2 * (C + 1)) with hc
  set x := (A.chart j).symm y with hx
  have hm : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x := ⟨hy, L.mem_U _⟩
  have hm' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Om.U x := ⟨hy, Om.mem_U _⟩
  have c1 := (contDiffAt_pot hO x j hm').of_le two_le_infty
  have c2 := (contDiffAt_pot hL x j hm).of_le two_le_infty
  have c3 := (contDiffAt_log_norm (hS.1 x j y hm) h0).of_le two_le_infty
  have e1 : (Om + LocPot.ofFun fun x => -c * r x).φ x ∘ (A.chart j).symm =ᶠ[𝓝 y] fun z =>
      ((Om.φ x ∘ (A.chart j).symm) z + (-2 * c) * (L.φ x ∘ (A.chart j).symm) z +
        (2 * c) * Real.log ‖(s x ∘ (A.chart j).symm) z‖) - c * Real.exp 1 := by
    filter_upwards [local_eventuallyEq hS hr j hy h0] with z hz
    show Om.φ x _ + -c * r _ = _
    rw [hz]
    simp only [Function.comp_apply]
    ring
  have h1 := hpsh x j y ⟨hy, Om.mem_U _, L.mem_U _⟩ w
  have h2 := TailBoundAlt.isPsh_of_isPosPot A Om hP x j y hm' w
  have e2 := TailChernBound.levi_lin C (-1) c1 c2 w
  have h3 : 0 ≤ C * levi (Om.φ x ∘ (A.chart j).symm) y w + (-1) * levi (L.φ x ∘ (A.chart j).symm) y w :=
    e2 ▸ h1
  rw [leviAt, ← hx, levi_congr e1, levi_sub_const, levi_add_smul _ (c1.add (contDiffAt_const.mul c2)) c3,
    levi_add_smul _ c1 c2, levi_log_norm (hS.1 x j y hm) h0]
  generalize levi (Om.φ x ∘ (A.chart j).symm) y w = a at *
  generalize levi (L.φ x ∘ (A.chart j).symm) y w = b at *
  have e3 : a + -2 * c * b + 2 * c * 0 = (a + (C * a + -1 * b)) / (C + 1) := by
    rw [hc]
    field_simp
    ring
  rw [e3]
  positivity

end BdSec

theorem isBd_of_isBdSec (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om L : LocPot X) (s : X → X → ℂ)
    (hO : IsPotential A Om) (hP : IsPosPot A Om) (h : IsBdSec A Z r L s) : IsBd A Z r Om := by
  have he := IsBdSec.exp_le A Z r h
  obtain ⟨hL, hS, -, rfl, hne, hr⟩ := h
  have hi := BdSec.interior_bdry hS hne
  exact ⟨isClosed_bdry hS, BdSec.bdry_null_chart hS hi, hO, hP, BdSec.smoothOn hL hS hr, he, BdSec.toBot hL hS hr,
    BdSec.mIntegrable hL hS hr hi fun _ => hO, BdSec.exists_pshOff hO hP hL hS hr⟩

end GlobalTheory.Mean4O
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorBoundWeierstrassCmTorsionStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_bound_weierstrass_cm_torsion : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (L : PeriodPair) (Ω P : ℂ) (M : ℕ), d.Prime → 4 < d → MulStable L (Complex.I * (Real.sqrt d : ℝ)) → Ω ^ 12 = latDisc L → ¬ l ∣ M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((s2 L + L.weierstrassP P) / Ω ^ 2) := by
  first | exact @GlobalTheory.CMSize.main | exact GlobalTheory.CMSize.main | (intros; apply GlobalTheory.CMSize.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEmbeddingDeterminantValueStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_embedding_determinant_value : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), ∃ r : NNReal, r ≠ 0 ∧ IsShift C v D ((γ : O →+* O).comp τ₀) r ∧ Real.log r = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  first | exact @GlobalTheory.DetInv.shift_linear_isom | exact GlobalTheory.DetInv.shift_linear_isom | (intros; apply GlobalTheory.DetInv.shift_linear_isom <;> assumption)
end

