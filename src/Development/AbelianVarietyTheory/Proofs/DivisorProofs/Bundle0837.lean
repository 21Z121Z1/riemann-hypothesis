import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0562
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealTopFormalLogConstOneStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_top_formalLog_constOne : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 → DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  first | exact @GlobalTheory.QLog.dIn_top_formalLog_map | exact GlobalTheory.QLog.dIn_top_formalLog_map | (intros; apply GlobalTheory.QLog.dIn_top_formalLog_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOrigin
section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstOrigin : GlobalTheory.VertUnits.DivConstOrigin := by
  have h₁ := GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin
  have h₂ := GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants
  have h₃ := GlobalTheory.T.divConst_origin_noeth_alt
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith GlobalTheory.VertUnits.DivConst
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh _ hPo b c s hs hbc
  have hPo' : P = GlobalTheory.KeyOriginCut.originIdeal T := hPo
  obtain ⟨E, _, _, _, _, _, Q, _, hQ, j, hj, b₁, c₁, hbc₁, hjb, hjc⟩ :=
    h₁ T O hT P φ hφ hsh hPo' b c s hs hbc
  obtain ⟨A, _, _, _, _, _, _, i, hi, hil, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, bA, cA, sA, hsA, hisA,
    hbcA, hjbA⟩ := h₂ T O hT E Q hQ j hj b₁ c₁ s hs hbc₁
  obtain ⟨a, w, haw⟩ := h₃ T O hT P φ hφ hsh hPo' A i hi hil EA QA hQA jA hjA bA cA sA hsA hbcA
  exact ⟨a, w, by rw [← hjb, ← hjbA, haw]⟩

end GlobalTheory.VertUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpreadStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedWeight_nodes_far_and_spread : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ, (∀ i : Fin N, W.kc ≤ (i : ℕ) → W.w τ / (2 * W.T) ≤ -(W.u1 τ i : ℝ) ∧ W.w τ / (4 * W.T) ≤ |(W.u' τ i : ℝ)|) ∧ ∀ i l : Fin N, (W.u' τ i : ℝ) - W.u' τ l ≤ 3 / 2 * W.w τ / W.T := by
  first | exact @GlobalTheory.MeanTop.nodes_far_and_spread | exact GlobalTheory.MeanTop.nodes_far_and_spread | (intros; apply GlobalTheory.MeanTop.nodes_far_and_spread <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_val_eq_zero_abelian : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (b : Γ(A.left, U)), (∀ z ∈ pre u.ex U, val u.ex U b z = 0) → b = 0 := by
  first | exact @GlobalTheory.ValInj.eq_zero_of_val_eq_zero | exact GlobalTheory.ValInj.eq_zero_of_val_eq_zero | (intros; apply GlobalTheory.ValInj.eq_zero_of_val_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributedIdealClassesOfHilbertClassFieldJStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equidistributed_idealClasses_of_hilbertClassFieldJ : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := by
  first | exact @GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ | exact GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ | (intros; apply GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudi
section
open scoped Classical

open MvPolynomial in
theorem GlobalTheory.JSW.PieriDeterminant.vdm_ne (n : ℕ) : Matrix.det (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) ≠ 0 := by
  have h : (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin n) ℤ))).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, id, Fin.revPerm_apply, Fin.val_rev]
    rw [show n - 1 - (j : ℕ) = n - ((j : ℕ) + 1) by omega]
  rw [h, Matrix.det_permute']
  refine mul_ne_zero (by simp [Units.ne_zero]) ?_
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact MvPolynomial.X_injective

namespace GlobalTheory.JSW.PieriDeterminant

theorem adj {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n)) :
    ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d + 1 → l a = l b → a ∉ J → b ∈ J →
      ∃ a' b' : Fin n, (b' : ℕ) = a' + 1 ∧ l a' = l b' ∧ a' ∉ J ∧ b' ∈ J := by
  intro d
  induction d with
  | zero => intro a b h1 h2 h3 h4; exact ⟨a, b, by omega, h2, h3, h4⟩
  | succ d ih =>
    intro a b h1 h2 h3 h4
    have hc : (a : ℕ) + 1 < n := by have := b.isLt; omega
    let c : Fin n := ⟨a + 1, hc⟩
    have hac : a ≤ c := by show (a : ℕ) ≤ a + 1; omega
    have hcb : c ≤ b := by show (a : ℕ) + 1 ≤ b; omega
    have hlc : l c = l a := le_antisymm (hl hac) (h2 ▸ hl hcb)
    by_cases hcJ : c ∈ J
    · exact ⟨a, c, rfl, hlc.symm, h3, hcJ⟩
    · exact ih c b (by show (b : ℕ) = a + 1 + d + 1; omega) (hlc.trans h2) hcJ h4

theorem det_zero {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n))
    (hJ : ¬ Antitone (l + (fun i => if i ∈ J then 1 else 0))) :
    Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
      ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) = 0 := by
  obtain ⟨a, b, hab, hlt⟩ : ∃ a b : Fin n, a ≤ b ∧ ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) a <
      ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) b := by
    simp only [Antitone, not_forall, not_le] at hJ
    obtain ⟨a, b, h1, h2⟩ := hJ; exact ⟨a, b, h1, h2⟩
  simp only [Pi.add_apply] at hlt
  have hla := hl hab
  have hA : a ∉ J := by intro h; simp only [h, if_true] at hlt; split_ifs at hlt <;> omega
  have hB : b ∈ J := by by_contra h; simp only [h, if_false] at hlt; split_ifs at hlt <;> omega
  have hE : l a = l b := by simp only [hA, hB, if_true, if_false] at hlt; omega
  have hne : a ≠ b := by rintro rfl; exact hA hB
  obtain ⟨a', b', h1, h2, h3, h4⟩ :=
    adj l hl J ((b : ℕ) - a - 1) a b (by have : (a : ℕ) < b := lt_of_le_of_ne hab (fun h => hne (Fin.ext h)); omega) hE hA hB
  refine Matrix.det_zero_of_column_eq (i := a') (j := b') (fun h => by rw [h] at h1; omega) (fun i => ?_)
  simp only [Matrix.of_apply, h3, h4, if_true, if_false]
  congr 1
  have := b'.isLt
  omega

end GlobalTheory.JSW.PieriDeterminant

open MvPolynomial in
theorem GlobalTheory.JSW.esymm_mul_schur : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  intro n l hl j _
  apply mul_right_cancel₀ (GlobalTheory.JSW.PieriDeterminant.vdm_ne n)
  have h1 := GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted n (fun k => l k + n - 1 - k) j
  beta_reduce at h1
  calc MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l * _
      = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        rw [mul_assoc, GlobalTheory.T.schur_mul_vandermonde_det_eq_det n l hl, h1]
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        refine (Finset.sum_filter_of_ne fun J _ hJ => ?_).symm
        by_contra h
        exact hJ (GlobalTheory.JSW.PieriDeterminant.det_zero l hl J h)
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) *
            Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [GlobalTheory.T.schur_mul_vandermonde_det_eq_det n _ (Finset.mem_filter.1 hJ).2]
        have e : ∀ k : Fin n, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) k + n - 1 - (k : ℕ) =
            (l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0 := by
          intro k; have := k.isLt; simp only [Pi.add_apply]; split_ifs <;> omega
        simp only [e]
    _ = _ := by rw [Finset.filter_filter, Finset.sum_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFieldEqGaloisCohomology
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.FieldTw

theorem res_ofRings_sec {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
    {V U : Scheme.{0}} (j : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res j (ofRings.sec M U x) = ofRings.sec M V ((M.map (Scheme.Γ.map j.op)).hom x) := by
  have h := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
  exact h.symm

theorem twF_map_mk {q : ℕ} (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q i).map f).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ) 1) := by
  change (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ 1)) :
    (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q i B) = _
  rw [Finsupp.mapDomain_single]

theorem res_twGen {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (j : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res j (twGen i ζ) = twGen i (Prim.map (Scheme.Γ.map j.op).hom ζ) := by
  unfold twGen
  refine (res_ofRings_sec (twF q i) j _).trans ?_
  exact congrArg (ofRings.sec (twF q i) V) (twF_map_mk i (Scheme.Γ.map j.op) ζ)

theorem quot_pow {q : ℕ} (i : ℤ) {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)) • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩

theorem twGen_pow {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen i ξ = (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)) • twGen i ζ := by
  have := congrArg (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom) (quot_pow i ζ ξ a h)
  exact this.trans (LinearMap.map_smul _ _ _)

theorem res_id' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

end GlobalTheory.EtC.FieldTw

namespace GlobalTheory.EtC.FieldTw

theorem cyclotomic_aeval_eq_zero {Ω : Type} [Field Ω] {q : ℕ} [NeZero q] {ζ : Ω} (hζ : IsPrimitiveRoot ζ q) :
    Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ.isRoot_cyclotomic (Nat.pos_of_ne_zero (NeZero.ne q))

theorem field_tw_coh_eq_galois : B7 := by
  intro q _ K Ω _ _ _ _ hq i M _ ζ hζ b hM n
  have hqΩ : IsUnit (q : Ω) := by simpa using hq.map (algebraMap K Ω)
  let S : Scheme.{0} := Spec (CommRingCat.of Ω)
  let ι : Ω →+* Γ(S, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  let ζ0 : Prim q Ω := ⟨ζ, hqΩ, cyclotomic_aeval_eq_zero hζ⟩
  let ζ' : Prim q Γ(S, ⊤) := Prim.map ι ζ0
  let g : Sec (tw q (i : ℤ)) S := twGen (i : ℤ) ζ'
  obtain ⟨e, he1, -⟩ := GlobalTheory.T.freeRankOne_etaleSheaf_equiv_locallyConstant (ZMod q) (tw q (i : ℤ)) S g (GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i S ζ')
  have hconst := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) Ω
  let φ : ZMod q →+ Sec (tw q (i : ℤ)) S :=
    { toFun := fun c => (ULift.up c : ULift.{1} (ZMod q)) • g
      map_zero' := by
        show (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • g = 0
        exact zero_smul _ _
      map_add' := fun a c => by
        show (ULift.up (a + c) : ULift.{1} (ZMod q)) • g = _
        rw [show (ULift.up (a + c) : ULift.{1} (ZMod q)) = ULift.up a + ULift.up c from rfl, add_smul] }
  have hφ : Function.Bijective φ := by
    have : (φ : ZMod q → Sec (tw q (i : ℤ)) S) = e S (𝟙 S) ∘ fun c => LocallyConstant.const S c := by
      funext c
      simp only [Function.comp_apply, he1, res_id']
      rfl
    rw [this]
    exact (e S (𝟙 S)).bijective.comp hconst
  let E1 : ZMod q ≃+ Sec (tw q (i : ℤ)) S := AddEquiv.ofBijective φ hφ
  let E0 : M ≃+ ZMod q := (b.equivFun.trans (LinearEquiv.funUnique Unit (ZMod q) (ZMod q))).toAddEquiv
  have hE0 : ∀ m, E0 m = b.repr m () := fun m => rfl
  refine GlobalTheory.T.nonempty_cohomology_addEquiv_galois_cohomology (ZMod q) (tw q (i : ℤ)) (GlobalTheory.T.tateTwist_finitary q i) K Ω M (E0.trans E1) ?_ n
  intro σ m

  have hσ : IsPrimitiveRoot (σ ζ) q := hζ.map_of_injective σ.injective
  obtain ⟨a, ha, hpow⟩ := hζ.eq_pow_of_pow_eq_one hσ.pow_eq_one
  have hcop : a.Coprime q := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) a).1 (hpow ▸ hσ)
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
  have hu : (u : ZMod q) = a := ZMod.coe_unitOfCoprime a hcop
  have hmρ := hM σ a hpow.symm

  have hm : m = b.repr m () • b () := by
    simpa using (b.sum_repr m).symm
  have hrep : b.repr (M.ρ σ m) () = b.repr m () * (a : ZMod q) ^ i := by
    have h1 : M.ρ σ m = (b.repr m () * (a : ZMod q) ^ i) • b () := by
      conv_lhs => rw [hm]
      rw [LinearMap.map_smul, hmρ, smul_smul]
    rw [h1, LinearEquiv.map_smul, b.repr_self]
    simp

  let ξ : Prim q Γ(S, ⊤) := Prim.map (Scheme.Γ.map (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))).op).hom ζ'
  have hξ : ξ.1 = ζ'.1 ^ (u : ZMod q).val := by
    rw [hu, ZMod.val_natCast, Nat.mod_eq_of_lt ha]
    show (Scheme.Γ.map (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))).op).hom (ι ζ) = (ι ζ) ^ a
    have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : Ω →+* Ω))
    have := congrArg (fun f => f.hom ζ) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← map_pow, hpow]
    try exact this.symm
  have hg : Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) g =
      (ULift.up ((a : ZMod q) ^ i) : ULift.{1} (ZMod q)) • g := by
    rw [res_twGen, twGen_pow (i : ℤ) ζ' ξ u hξ]
    congr 2
  show (ULift.up (E0 (M.ρ σ m)) : ULift.{1} (ZMod q)) • g = Sec.res _ ((ULift.up (E0 m) : ULift.{1} (ZMod q)) • g)
  have hlin : ∀ c : ULift.{1} (ZMod q), Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (c • g) =
      c • Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) g := fun c => LinearMap.map_smul _ _ _
  rw [hE0, hE0, hrep, hlin, hg, smul_smul]
  rfl

end GlobalTheory.EtC.FieldTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNhdsNEInChart
section
open CategoryTheory AlgebraicGeometry Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

variable {N : ℕ}

abbrev InChart (x : Sp ℂ ⟶ PSpace ℂ N) (i : Fin (N + 1)) : Prop := ⊤ ≤ x ⁻¹ᵁ chart ℂ N i

def rv (x : Sp ℂ ⟶ PSpace ℂ N) (i j : Fin (N + 1)) : ℂ := valAt' x (chart ℂ N i) (ratio ℂ N i j)

theorem rv_eq {x : Sp ℂ ⟶ PSpace ℂ N} {i : Fin (N + 1)} (h : InChart x i) (j : Fin (N + 1)) :
    rv x i j = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (pullRatio x ⊤ i h j) := by
  rw [rv, valAt', dif_pos h]
  rfl

theorem rv_self {x : Sp ℂ ⟶ PSpace ℂ N} {i : Fin (N + 1)} (h : InChart x i) : rv x i i = 1 := by
  rw [rv_eq h, pullRatio_self, map_one]

theorem rv_mul {x : Sp ℂ ⟶ PSpace ℂ N} {i j : Fin (N + 1)} (hi : InChart x i) (hj : InChart x j)
    (k : Fin (N + 1)) : rv x i j * rv x j k = rv x i k := by
  rw [rv_eq hi, rv_eq hj, rv_eq hi, ← map_mul, pullRatio_mul_pullRatio]

theorem inChart_iff {x : Sp ℂ ⟶ PSpace ℂ N} {i : Fin (N + 1)} (hi : InChart x i) (j : Fin (N + 1)) :
    InChart x j ↔ rv x i j ≠ 0 := by
  rw [rv, ← GlobalTheory.HolHom.le_basicOpen_iff x hi, ratio, basicOpen_ratioOn, Scheme.Hom.preimage_inf, le_inf_iff]
  exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩

theorem exists_inChart (x : Sp ℂ ⟶ PSpace ℂ N) : ∃ i, InChart x i :=
  (exists_mem_chart ℂ N (x (default : PrimeSpectrum ℂ))).imp fun _ h => (GlobalTheory.HolHom.le_preimage_iff x _).2 h

theorem eq_of_rv_eq {x y : Sp ℂ ⟶ PSpace ℂ N} (h : x ≫ PSpace.str ℂ N = y ≫ PSpace.str ℂ N) {i : Fin (N + 1)}
    (hx : InChart x i) (hy : InChart y i) (H : ∀ j, rv x i j = rv y i j) : x = y := by
  refine hom_ext h fun p => ⟨⊤, trivial, i, hx, hy, fun j => ?_⟩
  have := H j
  rw [rv_eq hx, rv_eq hy] at this
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 this

theorem inChart_pt (c : ℂ →+* ℂ) (v : Fin (N + 1) → ℂ) (hv : Ideal.span (Set.range v) = ⊤) {i : Fin (N + 1)}
    (hi : v i ≠ 0) : InChart (pt c v hv) i := by
  rw [InChart, pt_preimage_chart]
  intro p _
  rw [mem_spOpen]
  exact fun h => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsUnit.mk0 _ hi))

theorem rv_pt (c : ℂ →+* ℂ) (v : Fin (N + 1) → ℂ) (hv : Ideal.span (Set.range v) = ⊤) {i : Fin (N + 1)}
    (hi : v i ≠ 0) (j : Fin (N + 1)) : rv (pt c v hv) i j = v j / v i := by
  have h := inChart_pt c v hv hi
  have e : ∀ a : ℂ, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (fnOn ⊤ a) = a := fun a => by
    have : fnOn (A := ℂ) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a :=
      GlobalTheory.Cartier.resG_self (X := Sp ℂ) le_top _
    rw [this]
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply a
  rw [rv_eq h, eq_div_iff hi, ← e (v i), ← e (v j), ← map_mul, pullRatio_pt_mul]

section Hol

variable {φ ψ : ℂ → (Sp ℂ ⟶ PSpace ℂ N)}

theorem eventually_inChart (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z : ℂ} {i : Fin (N + 1)} (h : InChart (φ z) i) :
    ∀ᶠ w in 𝓝 z, InChart (φ w) i :=
  (GlobalTheory.HolHom.holAt_of_isHolTo hφ (Set.mem_univ z) _ h).1

theorem analyticAt_rv (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z : ℂ} {i : Fin (N + 1)} (h : InChart (φ z) i)
    (j : Fin (N + 1)) : AnalyticAt ℂ (fun w => rv (φ w) i j) z :=
  (hφ (chart ℂ N i) (ratio ℂ N i j)).2.analyticAt ((hφ _ (ratio ℂ N i j)).1.mem_nhds ⟨trivial, h⟩)

theorem eq_of_eventuallyEq (hφ : IsHolTo (Set.univ : Set ℂ) φ) (hψ : IsHolTo (Set.univ : Set ℂ) ψ) {z : ℂ}
    (hs : φ z ≫ PSpace.str ℂ N = ψ z ≫ PSpace.str ℂ N) (h : ∀ᶠ w in 𝓝[≠] z, φ w = ψ w) : φ z = ψ z := by
  obtain ⟨k, hk⟩ := exists_inChart (φ z)
  obtain ⟨l, hl⟩ := exists_inChart (ψ z)
  have key : ∀ j, rv (ψ z) l k * rv (φ z) k j = rv (ψ z) l j := fun j => by
    have h1 := ((analyticAt_rv hψ hl k).continuousAt.mul (analyticAt_rv hφ hk j).continuousAt).tendsto
    have h2 := (analyticAt_rv hψ hl j).continuousAt.tendsto
    refine tendsto_nhds_unique_of_eventuallyEq (h1.mono_left nhdsWithin_le_nhds)
      (h2.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))) ?_
    filter_upwards [h, nhdsWithin_le_nhds (eventually_inChart hφ hk), nhdsWithin_le_nhds (eventually_inChart hψ hl)]
      with w e a b
    rw [e] at a
    simp only [Pi.mul_apply, e]
    exact rv_mul b a j
  have h0 : rv (ψ z) l k ≠ 0 := left_ne_zero_of_mul_eq_one ((key l).trans (rv_self hl))
  have hk' : InChart (ψ z) k := (inChart_iff hl k).2 h0
  exact eq_of_rv_eq hs hk hk' fun j => mul_left_cancel₀ h0 ((key j).trans (rv_mul hl hk' j).symm)

theorem eventually_nhdsNE_inChart (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z₀ : ℂ} {k : Fin (N + 1)}
    (h₀ : InChart (φ z₀) k) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, InChart (φ w) k := by
  let A : Set ℂ := {z | ∀ᶠ w in 𝓝[≠] z, InChart (φ w) k}
  have dich : ∀ z, z ∈ A ∨ ∀ᶠ w in 𝓝 z, ¬ InChart (φ w) k := fun z => by
    obtain ⟨i, hi⟩ := exists_inChart (φ z)
    rcases (analyticAt_rv hφ hi k).eventually_eq_zero_or_eventually_ne_zero with h | h
    · right
      filter_upwards [h, eventually_inChart hφ hi] with w a b c using (inChart_iff b k).1 c a
    · left
      filter_upwards [h, nhdsWithin_le_nhds (eventually_inChart hφ hi)] with w a b using (inChart_iff b k).2 a
  have ho : IsOpen A := isOpen_iff_mem_nhds.2 fun z hz => by
    have hz' : ∀ᶠ w in 𝓝 z, w ≠ z → InChart (φ w) k := eventually_nhdsWithin_iff.1 hz
    filter_upwards [hz'] with w hw
    by_cases e : w = z
    · exact e ▸ hz
    · exact nhdsWithin_le_nhds (eventually_inChart hφ (hw e))
  have hc : IsOpen Aᶜ := isOpen_iff_mem_nhds.2 fun z hz => by
    filter_upwards [((dich z).resolve_left hz).eventually_nhds] with w hw
    intro (hA : ∀ᶠ u in 𝓝[≠] w, InChart (φ u) k)
    obtain ⟨u, a, b⟩ := (hA.and (nhdsWithin_le_nhds hw)).exists
    exact b a
  have hA : A = Set.univ := IsClopen.eq_univ ⟨isOpen_compl_iff.1 hc, ho⟩
    ⟨z₀, nhdsWithin_le_nhds (eventually_inChart hφ h₀)⟩
  exact hA.ge (Set.mem_univ z)

theorem meromorphic_rv (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z₀ : ℂ} {k : Fin (N + 1)}
    (h₀ : InChart (φ z₀) k) (j : Fin (N + 1)) : Meromorphic fun w => rv (φ w) k j := fun z => by
  obtain ⟨i, hi⟩ := exists_inChart (φ z)
  refine ((analyticAt_rv hφ hi j).meromorphicAt.div (analyticAt_rv hφ hi k).meromorphicAt).congr ?_
  filter_upwards [eventually_nhdsNE_inChart hφ h₀ z, nhdsWithin_le_nhds (eventually_inChart hφ hi)] with w a b
  rw [Pi.div_apply, div_eq_iff ((inChart_iff b k).1 a), mul_comm, rv_mul b a]

end Hol

end GlobalTheory.ProjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeRestrictOpenImmersionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_restrict_openImmersion : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ (V : Scheme.{0}) (j : V ⟶ S), IsOpenImmersion j → ∃ (A' : Over V) (_ : GrpObj A') (_ : IsCommMonObj A') (φ : A'.left ⟶ A.left), IsGrpPullback A' A j φ ∧ IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧ Out.RelAmple A' (L.pull φ) := by
  first | exact @GlobalTheory.OpenRestrictPol.exists_restrict_open | exact GlobalTheory.OpenRestrictPol.exists_restrict_open | (intros; apply GlobalTheory.OpenRestrictPol.exists_restrict_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineSpaceMorphismOfCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineSpace_morphism_of_coordinates : ∀ (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg) (x : Fin n → Γ(T, ⊤)), ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  first | (exact @GlobalTheory.HomFixPoint.exists_affine_hom) | (exact GlobalTheory.HomFixPoint.exists_affine_hom) | (intros; apply GlobalTheory.HomFixPoint.exists_affine_hom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriodStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod : ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ → Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra; ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic) (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point), GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ), GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ → ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  first | exact @GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | exact GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | (intros; apply GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjKernelMulStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_kernel_mul' : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ c : ℕ, ¬ p ∣ c ∧ ∀ k : ℕ, GlobalTheory.ConjPoint.IsConj L L σ ((k : ℂ) * t) ((k : ℂ) * ((c : ℂ) * t)) := by
  first | exact @GlobalTheory.CMModel.exists_conj_kernel_mul | exact GlobalTheory.CMModel.exists_conj_kernel_mul | (intros; apply GlobalTheory.CMModel.exists_conj_kernel_mul <;> assumption)
end

