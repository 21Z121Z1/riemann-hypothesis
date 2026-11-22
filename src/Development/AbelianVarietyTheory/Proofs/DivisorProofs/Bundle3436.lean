import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3427
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldOfTangentVectorOrigin
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3417
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousSwapRegular
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

theorem swapReg_exists : ArCalc → ∃ G, Homog G ∧ SwapReg G := by
  intro hC
  obtain ⟨G, hG, hcore⟩ := GlobalTheory.T.regular_base_rank_two_metric_family hC
  refine ⟨G, hG, ?_⟩
  intro k _ B Y _ _ q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ a b
  obtain ⟨flB⟩ := hflB
  set L5 := fam5 π w H flB fl A with hL5
  obtain ⟨Φ5, hΦ5⟩ := ((hC.arExists k Y p (d + 1) hp).2 (Fin 5) L5).1

  have e3 := GlobalTheory.VertForm.FormEx.arFun_eq_rename hC hp hΦ hΦ5 ![0, 1, 2] (fun i => by fin_cases i <;> rfl)

  have iso : ((L5 0).tens (L5 1)).Isometric ((L5 3).tens (L5 4)) := by
    have e₁ := GlobalTheory.T.rank_two_graded_determinant_isometric k Y p _ _ (H.pull π w) fl
    have e₂ := VMetric.isometric_det_pull H π w
    have e₃ := ((GlobalTheory.T.rank_two_graded_determinant_isometric k B q E h H flB).symm.pull π w).trans (HermLB.isometric_pull_tens _ _ π w)
    exact e₁.trans (e₂.trans e₃)
  have icl : (L5 1).icls = (L5 3).icls + (L5 4).icls - (L5 0).icls := by
    have := HermLB.icls_eq_iff.2 iso
    rw [HermLB.icls_tens, HermLB.icls_tens] at this
    rw [← this]
    abel

  let T : Fin 5 → Fin 5 → ℤ := fun j => if j = 1 then ![-1, 0, 0, 1, 1] else Pi.single j 1
  have hT : ∀ j, (comb L5 (T j)).Isometric (L5 j) := by
    intro j
    by_cases hj : j = 1
    · subst hj
      refine HermLB.icls_eq_iff.1 ?_
      rw [icls_comb, icl]
      simp [T, Fin.sum_univ_five]
      abel
    · simp only [T, hj, if_false]
      exact isometric_comb_single L5 j
  have hsub := ((hC.arIso k Y p (d + 1) hp).2 (Fin 5) L5 Φ5 hΦ5).2.2 (Fin 5) L5 T hT
  have e5 := GlobalTheory.ArInt.Model.isArFun_unique hp hΦ5 hsub
  have eline : Φ (lin ![(a : ℝ), b, 1] ^ (d + 2)) + Φ (lin ![(b : ℝ), a, 1] ^ (d + 2)) = Φ5 (onLine d a b) := by
    rw [← map_add, e3, LinearMap.comp_apply, AlgHom.toLinearMap_apply, e5, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    change Φ5 (aeval _ (rename _ (swapSum d a b))) = _
    rw [onLine, aeval_rename]
    congr 2
    congr 1
    funext i
    fin_cases i <;> simp [T, lin, Fin.sum_univ_five, Pi.single_apply] <;> ring

  have hdim : topologicalKrullDim (closure ({π (genericPoint Y)} : Set B)) < ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    refine (topologicalKrullDim_subspace_le B _).trans_lt ?_
    rw [hq.dim_eq]
    exact_mod_cast Nat.lt_succ_self (d + 1)
  let LB3 : Fin 3 → HermLB q := ![VMetric.grLB flB 1 H, VMetric.grLB flB 0 H, A]
  let L3 : Fin 3 → HermLB p := fun i => (LB3 i).pull π w
  obtain ⟨Φ3, hΦ3⟩ := ((hC.arExists k Y p (d + 1) hp).2 (Fin 3) L3).1
  have z3 : IsArFun L3 (d + 1) 0 := by
    refine ⟨fun n => ?_, fun _ _ _ _ => rfl⟩
    rw [LinearMap.zero_apply]
    exact (isometric_comb_pull LB3 n π w).symm.isSelfInter hp
      (GlobalTheory.ProjDrop.isSelfInter_zero_of_dim_lt hC k B Y q p d (d + 1) hq hp π w hdim (comb LB3 n))
  have e3' := GlobalTheory.VertForm.FormEx.arFun_eq_rename hC hp hΦ3 hΦ5 ![4, 3, 2] (fun i => by fin_cases i <;> rfl)
  have ebase : Φ5 (onBase d a b) = 0 := by
    have h0 := GlobalTheory.ArInt.Model.isArFun_unique hp hΦ3 z3
    have : onBase d a b = rename ![(4 : Fin 5), 3, 2] (swapSum d a b) := by
      rw [onBase, ← aeval_X_left_apply (rename _ _), aeval_rename]
      congr 2
      funext i
      fin_cases i <;> rfl
    rw [this, ← AlgHom.toLinearMap_apply, ← LinearMap.comp_apply, ← e3', h0, LinearMap.zero_apply]

  rw [eline, show onLine d a b = onBase d a b + (onLine d a b - onBase d a b) by ring, map_add, ebase, zero_add]
  exact hcore k B Y q p d hq hp hreg π w E h H flB fl hfl A Φ5 Ψ hΦ5 hΨ a b

end GlobalTheory.CovTest.SwapLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryDivisibleOfQuasiLogDefec
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem exists_int_cob_dvd_of_defect_ev :
    ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  intro p _ O E _ _ _ hF G d c f s y hQL hs hy
  obtain ⟨hf0, -, hcob⟩ := hQL
  choose bκ _ hbκ using hcob
  set κ : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => bκ α with hκdef
  have hκ : map (algebraMap O E) κ = cob1 (up E c.μ) f := by
    ext α
    rw [coeff_map, hbκ α]
    rfl
  obtain ⟨hcoc, hκ0, hdef⟩ := GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hrel := (hdef p s hs).1
  have hμ0 := c.isLaw.const
  have hneg : cob1 c.μ (-s) = -cob1 c.μ s := by
    rw [← neg_one_smul O s, formalCoboundary_smul hμ0, neg_one_smul]
  obtain ⟨t, ht0, htd⟩ := GlobalTheory.T.formalGroupCocycle_coboundary_mod_prime p O G d c κ (-s) (-y) (hκ0 hf0) hcoc
    (fun α => by
      rw [hneg, hrel, show -((p : O) • κ - pull2 (nmul c.μ p) κ) - pull2 (nmul c.μ p) κ
        = -((p : O) • κ) by ring, map_neg, coeff_smul]
      exact (Dvd.intro _ rfl).neg_right)
    (by rw [map_neg, hy, smul_neg])
  refine ⟨t, ht0, fun α => ⟨coeff α (κ - cob1 c.μ t), Ideal.mem_span_singleton.2 (htd α), ?_⟩⟩
  have hup0 : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ0, map_zero]
  have hadd := formalCoboundary_add hup0 (f - map (algebraMap O E) t) (map (algebraMap O E) t)
  rw [sub_add_cancel] at hadd
  have hmap := (GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hμ0 E (algebraMap O E)).1 t
  have hsub : cob1 (up E c.μ) (f - map (algebraMap O E) t) =
      map (algebraMap O E) (κ - cob1 c.μ t) := by
    rw [map_sub, hmap, hκ]
    exact eq_sub_of_add_eq hadd.symm
  rw [hsub, coeff_map]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFieldCoefficientsOfLinearVectorFi
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VertCoeffRing
open GlobalTheory.TangentOrigin
open GlobalTheory.KS (rsT_add rsT_mul rsT_zero)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem evalPt_lieExp {m : ℕ} (u : Fin m → TanM (𝟙 (Sp R)) G) (dd : Fin m → Fld G.left)
    (hd : ∀ i, IsInv G (u i) (dd i)) (B : Type) [CommRing B] [Algebra R B] (e : Fin m → B)
    (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction m with
  | zero =>
    have : GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z = z := by
      simp [GlobalTheory.SqZero.lieExp]
    rw [this]
    exact ⟨h, fun f => by simp⟩
  | succ m ih =>
    obtain ⟨h₁, H₁⟩ := ih (fun i => u i.succ) (fun i => dd i.succ) (fun i => hd i.succ) (fun i => e i.succ)
      (fun i j => he _ _)
    obtain ⟨h₂, H₂⟩ := GlobalTheory.T.value_at_invariantField_translate_sqZero (hd 0) (e 0) (he 0 0) _ O h₁
    have : GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e 0) (he 0 0)) ≫ tvE (u 0)) *
          (GlobalTheory.SqZero.lieExp (fun i => tvE (u i.succ)) (fun i => e i.succ) (fun i => he i.succ i.succ) * z) := by
      rw [GlobalTheory.SqZero.lieExp, GlobalTheory.SqZero.lieExp, Fin.prod_univ_succ, _root_.mul_assoc]
    rw [this]
    refine ⟨h₂, fun f => ?_⟩
    rw [H₂, H₁, H₁, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    simp only [← _root_.mul_assoc, he, zero_mul, Finset.sum_const_zero]
    ring

theorem exists_coeff : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) →
    ∀ (W : G.left.Opens) (δ : Fld G.left), IsField W δ → (∀ O, O ≤ W → ∀ r, δ O (constFn G.hom O r) = 0) →
    ∃ c : Fin n → Γ(G.left, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  intro R _ G _ _ hs n v dd hd W δ hδ hc
  have hb := GlobalTheory.T.isLieBasis_dualPoints_of_tangentModule_basis v
  refine GlobalTheory.T.exists_vectorField_coeffs_glued_from_affineOpens W δ dd hδ (fun a => (hd a).1) fun V V' hV hV' hVW hV'V => ?_
  exact GlobalTheory.T.existsUnique_lieBasis_coeffs_of_derivation_affineOpen _ hb dd (fun B _ _ e he z O h => evalPt_lieExp v dd hd B e he z O h) V V' hV hV' hV'V
    (fun f => rsT (δ V f) V') (fun f f' => by simp only [hδ.1 V hVW, rsT_add])
    (fun f f' => by simp only [hδ.2.1 V hVW, rsT_add, rsT_mul])
    (fun r => by simp only [hc V hVW r, rsT_zero])

end GlobalTheory.VertCoeffRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldSemiAbelianTripleAffin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.InvFieldSemiAb

theorem exists_isInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v : TanM (𝟙 (Sp R)) t.G), ∃ dd : Fld t.G.left, IsInv t.G v dd := by
  intro E _ _ _ H R _ t v
  exact GlobalTheory.InvFieldBase.exists_isInv R t.G v

end GlobalTheory.InvFieldSemiAb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKsCocOfKsRel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSCechData

open GlobalTheory.KS GlobalTheory.LogKSBal

theorem constFn_spMap {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) {Y : Scheme.{0}} (q : Y ⟶ Sp K)
    (O : Y.Opens) (r : R) : constFn (q ≫ spMap x₀) O r = constFn q O (x₀ r) := by
  refine ext_valR _ _ fun B _ y hy => ?_
  have e : y ≫ q = spMap (Spec.preimage (y ≫ q)).hom := (Spec.map_preimage _).symm
  generalize (Spec.preimage (y ≫ q)).hom = β at e
  rw [valR_constFn q y hy e, valR_constFn (q ≫ spMap x₀) y hy (β := β.comp x₀)
    (by rw [← Category.assoc, e, GlobalTheory.LogKSLoc.spMap_comp'])]
  rfl

theorem constFn_neg {K : Type} [CommRing K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (r : K) :
    constFn q O (-r) = -constFn q O r := by
  simp [constFn]

theorem exists_ksCoc_of_ksRel : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ P.A.left), m ≫ P.A.hom = A.hom ≫ spMap x₀ → ∀ {g : ℕ} (e : Fin g → Fld P.A.left) (dd : Fin g → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ a, IsField ⊤ (e a)) → (∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → ∃ L : LB P.A.left, Finite L.ι ∧ L.IsLB ∧ (∀ i, IsAffineOpen (L.U i)) ∧ LBIso P.L L ∧ ∃ d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(A.left, m ⁻¹ᵁ O), ∀ φ, GlobalTheory.KS.IsDlog m L dd φ → GlobalTheory.KS.KSCoc A.hom P.A.hom m (fun r => x₀ (D r)) L.U dd d (fun a => GlobalTheory.KS.lc A.hom (fun b => -x₀ (M a b)) φ) := by
  intro R _ K _ x₀ P A _ m hm g e dd he hdd D M hKS
  obtain ⟨J, W, j, d, hcov, hWj, hlift, hdiff⟩ := hKS
  have := P.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have hloc : ∀ x : P.A.left, ∃ (Ω : P.A.left.Opens) (k : J), IsAffineOpen Ω ∧ x ∈ Ω ∧ Ω ≤ W k := by
    intro x
    have h2 : x ∈ ⨆ k, W k := by
      rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    obtain ⟨_, ⟨Ω, hΩ, rfl⟩, hx, hle⟩ := P.A.left.isBasis_affineOpens.exists_subset_of_mem_open hk (W k).isOpen
    exact ⟨Ω, k, hΩ, hx, hle⟩
  obtain ⟨s, hfin, Ω, κ, hΩ, hΩW, hs⟩ : ∃ (s : Type) (_ : Finite s) (Ω : s → P.A.left.Opens) (κ : s → J),
      (∀ a, IsAffineOpen (Ω a)) ∧ (∀ a, Ω a ≤ W (κ a)) ∧ ⨆ a, Ω a = ⊤ := by
    choose Ω κ hΩ hxΩ hΩW using hloc
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (Ω x : Set P.A.left))
      (fun x => (Ω x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxΩ x⟩)
    refine ⟨s, inferInstance, fun a => Ω a, fun a => κ a, fun a => hΩ a, fun a => hΩW a, top_le_iff.1 fun x _ => ?_⟩
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  have hle : ∀ a : s, Ω a ≤ P.L.U (j (κ a)) := fun a => (hΩW a).trans (hWj (κ a))
  let L := GlobalTheory.FinAffineCharts.refineLB P.L Ω (fun a => j (κ a)) hle
  have happ : ∀ (O : P.A.left.Opens) (f : Γ(P.A.left, O)), (m.app O).hom f = pbT m f (m ⁻¹ᵁ O) :=
    fun O f => GlobalTheory.KS.AdjDlog.app_eq_pbT m O f
  have hconst : ∀ (O : P.A.left.Opens) (r : R), pbT m (constFn P.A.hom O r) (m ⁻¹ᵁ O) =
      constFn A.hom (m ⁻¹ᵁ O) (x₀ r) := fun O r => by
    rw [pbT_constFn _ _ le_rfl, hm, constFn_spMap]
  refine ⟨L, hfin, GlobalTheory.FinAffineCharts.refineLB_isLB P.isLB _ _ hle hs,
    fun a => hΩ a, GlobalTheory.FinAffineCharts.iso_refineLB P.isLB _ _ hle,
    fun a O f => pbT m (d (κ a) O f) _, fun φ hφ => ⟨fun a => ⟨fun O hO f f' => ?_, fun O hO f f' => ?_,
      fun O O' h hO f => ?_, fun O hO r => ?_⟩, fun a b O hO f => ?_⟩⟩
  · rw [(hlift _).1.1 _ (hO.trans (hΩW a)), pbT_add]
  · rw [(hlift _).1.2.1 _ (hO.trans (hΩW a)), pbT_add, pbT_mul, pbT_mul, happ, happ]
  · rw [(hlift _).1.2.2 _ _ h (hO.trans (hΩW a)), ← rsT_of_le h, pbT_rsT _ h le_rfl,
      rsT_pbT _ le_rfl (m.preimage_mono h)]
  · rw [(hlift _).2 _ (hO.trans (hΩW a)), hconst]
  · have hO' : O ≤ Ω a ⊓ Ω b := hO
    have hU : Ω a ⊓ Ω b ≤ P.L.U (j (κ a)) ⊓ P.L.U (j (κ b)) := inf_le_inf (hle a) (hle b)
    have hab : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b := m.preimage_mono hO
    have hab' : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ (Ω a ⊓ Ω b) := m.preimage_mono hO
    have hg : (L.g a b).val = rsT (P.L.g (j (κ a)) (j (κ b))).val (Ω a ⊓ Ω b) :=
      GlobalTheory.KS.AdjDlog.val_res hU _
    have hφ' : ∀ c, rsT (φ c a b) (m ⁻¹ᵁ O) =
        pbT m (dlg P.A (𝟙 P.A.left) P.L (e c) (j (κ a)) (j (κ b)) O) (m ⁻¹ᵁ O) := fun c => by
      have h₁ : pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) * φ c a b =
          pbT m (e c (Ω a ⊓ Ω b) (L.g a b).val) (m ⁻¹ᵁ (Ω a ⊓ Ω b)) :=
        (hφ c a b).trans ((congrArg (dd c (m ⁻¹ᵁ (Ω a ⊓ Ω b))) (happ (Ω a ⊓ Ω b) (L.g a b).val).symm).trans
          (hdd c (Ω a ⊓ Ω b) (L.g a b).val))
      have h₂ : rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) * φ c a b) (m ⁻¹ᵁ O) =
          rsT (pbT m (e c (Ω a ⊓ Ω b) (L.g a b).val) (m ⁻¹ᵁ (Ω a ⊓ Ω b))) (m ⁻¹ᵁ O) :=
        congrArg (rsT · (m ⁻¹ᵁ O)) h₁
      have h₃ : rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b)) (m ⁻¹ᵁ O) =
          pbT m (P.L.g (j (κ a)) (j (κ b))).val (m ⁻¹ᵁ O) :=
        (rsT_pbT m (O₀ := Ω a ⊓ Ω b) (fun p hp => hp) hab _).trans
          ((congrArg (pbT m · (m ⁻¹ᵁ O)) hg).trans (pbT_rsT m hU hab' _))
      have h₄ : rsT (e c (Ω a ⊓ Ω b) (L.g a b).val) O = e c O (rsT (P.L.g (j (κ a)) (j (κ b))).val O) := by
        refine (rsT_of_le hO' _).trans (((he c).2.2 _ _ hO' le_top _).symm.trans (congrArg (e c O) ?_))
        refine (rsT_of_le (O₀ := Ω a ⊓ Ω b) hO' _).symm.trans ?_
        rw [← rsT_rsT hU hO']
        exact congrArg (fun z => rsT z O) hg
      rw [rsT_mul, h₃, rsT_pbT m le_rfl hab', ← pbT_rsT m hO' le_rfl, h₄] at h₂
      rw [dlg, GlobalTheory.KS.AdjDlog.pbT_id _ _ (hO'.trans hU), GlobalTheory.KS.AdjDlog.pbT_id _ _ (hO'.trans hU), pbT_mul, ← h₂,
        pbT_rsT m (hO'.trans hU) le_rfl, mul_right_comm, ← pbT_mul, Units.mul_inv,
        pbT_one m (m.preimage_mono (hO'.trans hU)), _root_.one_mul]
    have key := hdiff (κ a) (κ b) O (hO'.trans (inf_le_inf (hΩW a) (hΩW b))) f
    rw [← pbT_sub, ← neg_sub, key, pbT_neg, pbT_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hdd, lc, rsT_sum, Finset.sum_mul, pbT_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [rsT_mul, rsT_constFn _ hab, hφ', pbT_mul, pbT_mul, hconst, constFn_neg]
    ring

end GlobalTheory.KSCechData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_abelianLocus_toroidalChart : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → TorsRat G₁ n → ∀ (K : Type) [Field K] (κ : Localization.Away (∏ k, C.t k) →+* K) (x₀ : Sp K ⟶ F.X), x₀ ≫ F.s = spMap ((κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) → SameFib F.univ.A F.univ.P x₀ G₁ P (spMap (κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))))) → ∃ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal ∧ (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) ∧ ∀ yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X, SiegPB c F.univ yU → yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) → spMap κ ≫ yU = x₀ := by
  first | exact @GlobalTheory.TChart.AbLevel.exists_level | exact GlobalTheory.TChart.AbLevel.exists_level | (intros; apply GlobalTheory.TChart.AbLevel.exists_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifDvrBaseChange

theorem exists_pelUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ f : V →+* W, Function.Injective f → IsLocalHom f →
    ∀ tW : SAB H (Sp W), Nonempty (SABMap tW t (spMap f)) →
      ∃ (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X),
        ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : Wˣ, PsiCoord PW.D.toPre y (u * f r) := by
  intro E _ _ _ H V _ _ _ hV t P W _ _ _ hW hWd f hfi hfl tW ⟨m⟩
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨⟨hWN, -, hWI, hWc⟩, hW0⟩ := hW
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws

  have j : Function.Injective ((algebraMap W (FractionRing W)).comp f) := (IsFractionRing.injective W _).comp hfi
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  have eg : jK W ≫ spMap f = spMap g ≫ jK V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hpW : GlobalTheory.LN.PolAt tW (jK W) := GlobalTheory.DatUniq.polAt_pull m (GlobalTheory.DatUniq.polAt_of_unif P) (jK W) (spMap g) eg.symm
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W tW hpW

  have := t.semi.separated
  have := t.semi.smooth
  let p₀ : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ abLocus t.G := by
    rw [← GlobalTheory.TraitChartForm.jK_apply_eq_bot V p₀]
    exact (GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff t.G (IsPullback.of_hasPullback t.G.hom (jK V)) p₀).2
      (GlobalTheory.DatUniq.polAt_of_unif P).1

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let Wv : Set (Sp V) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Wv :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hne : Wv ≠ Set.univ := fun h => by
    have : closedPoint V ∈ Wv := h ▸ Set.mem_univ _
    exact this.2 hϖ.not_isUnit
  have hψ : ∀ y, PsiUnitOn P.D.toPre y Wv := fun y => GlobalTheory.DvrDataCompare.psiUnitOn_of_ne_univ P.D.toPre y hne
  have hker : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) ∈ Wv := by
    have hk : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) = ⟨⊥, Ideal.isPrime_bot⟩ :=
      PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)
    rw [hk]
    exact ⟨hgen, fun h => hϖ.ne_zero ((Submodule.mem_bot V).1 h)⟩
  have hloc : ∀ a ∈ maximalIdeal V, f a ∈ maximalIdeal W := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  obtain ⟨PW, e, he⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H V W f t tW m P Wv inferInstance inferInstance
    hVc hWN hWI hWc hloc hWo Set.inter_subset_left hψ hker ⟨B, gen, hg, hw⟩
  refine ⟨PW, e.symm, fun y r hr => ?_⟩
  obtain ⟨u, hu⟩ := he _ r hr
  exact ⟨u, by simpa using hu⟩

end GlobalTheory.UnifDvrBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullbackStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logDeriv_polarization_raynaud_eq_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left) (M : Fin n → Fin g → R) (N : Fin g → Fin n → R), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) ∧ (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) ∧ (∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) ∧ ∀ (b : Fin n) (i i' : Dd.toPre.P.L.ι) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i') → dlg Y.H Y.q.left Dd.toPre.P.L (dd b) i i' W = pbT Y.q.left (∑ a, constFn Dd.toPre.P.A.hom _ (M b a) * dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) i i' (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i')) W := by
  first | exact @GlobalTheory.Heat.LiePush.exists_dlg_eq_pbT | exact GlobalTheory.Heat.LiePush.exists_dlg_eq_pbT | (intros; apply GlobalTheory.Heat.LiePush.exists_dlg_eq_pbT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipallyPolarisedPowerUnimodularFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principally_polarised_power_unimodular_form : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ LBIso P'.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)) := by
  first | exact @GlobalTheory.Mum.TensPow.exists_pow_data_polAV | exact GlobalTheory.Mum.TensPow.exists_pow_data_polAV | (intros; apply GlobalTheory.Mum.TensPow.exists_pow_data_polAV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_invariantField_const_coeffs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ ℓ : Dd.toPre.X →+ R, ∃ c : Fin n → R, GlobalTheory.HeatMod.IsTorField Y (GlobalTheory.HeatMod.combF Y.H.hom dd c) ℓ := by
  first | exact @GlobalTheory.HeatMod.TorField.exists_isTorField | exact GlobalTheory.HeatMod.TorField.exists_isTorField | (intros; apply GlobalTheory.HeatMod.TorField.exists_isTorField <;> assumption)
end

