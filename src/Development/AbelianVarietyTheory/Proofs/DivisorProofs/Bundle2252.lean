import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesExist
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SURepsExist

open Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

theorem isUA_mul {g g' : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (hg' : IsUA c G g') :
    IsUA c G (g * g') := by
  refine ⟨by rw [det_mul]; exact hg.1.mul hg'.1, fun x y => ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hg'.2]

theorem isUA_of_inv {g g' : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (h1 : g * g' = 1) :
    IsUA c G g' := by
  refine ⟨IsUnit.of_mul_eq_one g.det (by rw [mul_comm, ← det_mul, h1, det_one]), fun x y => ?_⟩
  rw [← hg.2, mulVec_mulVec, mulVec_mulVec, h1, one_mulVec, one_mulVec]

variable {L : Set (Fin n → E)}

theorem stabilizer_maps_lattice_completion {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L 1 k) {x : Fin n → RA F E}
    (hx : x ∈ hat F L) : k *ᵥ x ∈ hat F L := by
  obtain ⟨y, hy, e⟩ := hk.2.1 x hx
  rw [one_nsmul, sub_eq_iff_eq_add] at e
  rw [e]; exact (hat F L).add_mem hy hx

theorem stabilizer_of_maps_onto {k : Matrix (Fin n) (Fin n) (RA F E)} (hU : IsUA c G k)
    (hm : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L) (hs : ∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ y = x) :
    IsKM c G L 1 k :=
  ⟨hU, fun x hx => ⟨k *ᵥ x - x, (hat F L).sub_mem (hm x hx) hx, by rw [one_nsmul]⟩, hs⟩

theorem stabilizer_mul {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L 1 k) (hk' : IsKM c G L 1 k') :
    IsKM c G L 1 (k * k') := by
  refine stabilizer_of_maps_onto c G (isUA_mul c G hk.1 hk'.1) (fun x hx => ?_) (fun x hx => ?_)
  · rw [← mulVec_mulVec]; exact stabilizer_maps_lattice_completion c G hk (stabilizer_maps_lattice_completion c G hk' hx)
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    obtain ⟨z, hz, rfl⟩ := hk'.2.2 y hy
    exact ⟨z, hz, by rw [mulVec_mulVec]⟩

theorem stabilizer_inv {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L 1 k) (h1 : k * k' = 1)
    (h2 : k' * k = 1) : IsKM c G L 1 k' := by
  refine stabilizer_of_maps_onto c G (isUA_of_inv c G hk.1 h1) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    rwa [mulVec_mulVec, h2, one_mulVec]
  · exact ⟨k *ᵥ x, stabilizer_maps_lattice_completion c G hk hx, by rw [mulVec_mulVec, h2, one_mulVec]⟩

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E))

theorem isSA_mul {g g' : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)} (hg : IsSA G g)
    (hg' : IsSA G g') : IsSA G (g * g') :=
  ⟨isUA_mul _ G hg.1 hg'.1, by rw [det_mul, hg.2, hg'.2, one_mul]⟩

theorem isSA_of_inv {g g' : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)} (hg : IsSA G g)
    (h1 : g * g' = 1) : IsSA G g' :=
  ⟨isUA_of_inv _ G hg.1 h1, by
    have := congrArg Matrix.det h1
    rwa [det_mul, hg.2, one_mul, det_one] at this⟩

theorem ratM_inv (γ : Matrix (Fin r) (Fin r) E) (hγ : IsSA G (ratM (maximalRealSubfield E) γ)) :
    ratM (maximalRealSubfield E) γ * ratM (maximalRealSubfield E) γ⁻¹ = 1 ∧
    ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ = 1 := by
  by_cases h : γ.det = 0
  · have e : (ratM (maximalRealSubfield E) γ).det = 0 := by
      have := (Algebra.TensorProduct.includeRight :
        E →ₐ[maximalRealSubfield E] RA (maximalRealSubfield E) E).map_det γ
      rw [h, map_zero] at this
      exact this.symm
    rw [hγ.2] at e
    haveI : Subsingleton (RA (maximalRealSubfield E) E) := subsingleton_of_zero_eq_one e.symm
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · have hu : IsUnit γ.det := isUnit_iff_ne_zero.mpr h
    rw [← ratM_mul, ← ratM_mul, mul_nonsing_inv γ hu, nonsing_inv_mul γ hu, ratM_one]
    exact ⟨rfl, rfl⟩

def sSetoid : Setoid {g // IsSA G g} where
  r a b := SEquiv G L 1 a.1 b.1
  iseqv := by
    refine ⟨fun a => ⟨1, by rw [ratM_one]; exact ⟨⟨by simp, fun x y => by simp⟩, by simp⟩,
      1, isKM_one _ G L 1, by simp, by rw [ratM_one]; simp⟩, ?_, ?_⟩
    · rintro a b ⟨γ, hγ, k, hk, hdk, e⟩
      have hr := ratM_inv G γ hγ
      have hku : IsUnit k.det := by rw [hdk]; exact isUnit_one
      refine ⟨γ⁻¹, isSA_of_inv G hγ hr.1, k⁻¹, stabilizer_inv _ G hk (mul_nonsing_inv k hku)
        (nonsing_inv_mul k hku), ?_, ?_⟩
      · rw [det_nonsing_inv, hdk, Ring.inverse_one]
      · rw [e]
        calc a.1 = (ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ) * a.1 * (k * k⁻¹) := by
                rw [hr.2, mul_nonsing_inv k hku]; simp
          _ = _ := by simp only [Matrix.mul_assoc]
    · rintro a b d ⟨γ, hγ, k, hk, hdk, e⟩ ⟨γ', hγ', k', hk', hdk', e'⟩
      refine ⟨γ' * γ, by rw [ratM_mul]; exact isSA_mul G hγ' hγ, k * k', stabilizer_mul _ G hk hk',
        by rw [det_mul, hdk, hdk', one_mul], ?_⟩
      rw [e', e, ratM_mul]; simp only [Matrix.mul_assoc]

theorem exists_sReps : ∃ (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)),
    IsSReps G L 1 s := by
  letI := sSetoid G L
  refine ⟨Quotient (sSetoid G L), fun q => q.out.1, fun q => q.out.2, fun i j h => ?_, fun g hg => ?_⟩
  · rw [← Quotient.out_eq i, ← Quotient.out_eq j]
    exact Quotient.sound h
  · exact ⟨⟦⟨g, hg⟩⟧, Quotient.mk_out (s := sSetoid G L) ⟨g, hg⟩⟩

end CM

end GlobalTheory.SURepsExist

theorem GlobalTheory.SURepsExist.main : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSReps (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) 1 s := by
  intro D Tu Cl t0 _ i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  exact GlobalTheory.SURepsExist.exists_sReps _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh
open GlobalTheory.TopForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_ord_sub_one_le_ord_wedgeDifferentials : ∀ {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    [LocallyOfFiniteType p] {n : ℕ}, topologicalKrullDim X = n → ∀ (E : DivOver p) {U : X.Opens} {y : X}
    (hy : y ∈ U), E.Through y → ∀ (z : Fin n → Γ(X, U)), formOf U (gen_mem hy) (dOn p z) ≠ 0 →
    ∀ {J : Type} [Fintype J] (e : J → Fin n), Function.Injective e → ∀ (u : J → X.functionFieldˣ),
    (∀ j, (u j : X.functionField) = fnOf U (gen_mem hy) (z (e j))) →
    ∑ j, E.ord (u j) - 1 ≤ E.formOrd (formOf U (gen_mem hy) (dOn p z)) := by
  first | exact @GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn | exact GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn | (intros; apply GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupConstantLogBoundStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sup_constant_log_bound : ∀ (D : D7) (M : ℕ) (Lb w : ℝ), 1 ≤ M → 1 ≤ Lb → Real.log M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → 1 ≤ w → Real.log w ≤ 25 * Lb → 1 ≤ GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d M w ∧ Real.log (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d M w) ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  first | exact @GlobalTheory.ConstSzRows.supConst_size_rows | exact GlobalTheory.ConstSzRows.supConst_size_rows | (intros; apply GlobalTheory.ConstSzRows.supConst_size_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricThetaTranslatesExpandSeriesFamilies
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic GlobalTheory.UT.SymFrame GlobalTheory.Ex.GtValues GlobalTheory.Ex.CoordSeries

theorem symTranslate_expandsF : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → ∀ m : ℕ, Odd m → ∀ (p : QkPt D.toPre C (m ^ 2)) (q : N.QT (m ^ 2)) (z : TFK (R := V) C ⟶ A.A), ν.QPt p q → QkToAkU U.toUnifPre C (m ^ 2) p z → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ IsEvFam N m q f ∧ ν.FamV s (c • f) := by
  intro V _ _ _ _ hcpl D A G _ _ hG U C _ _ _ _ _ _ hC N ν _ w₀ ρ hN th ϑ c hth hϑ m hm p q z hq hz
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hLB := A.isLB
  let y : Sp C := IsLocalRing.closedPoint C

  have hgt : ∀ b : N.A, ∃ h : N.Gt, h.b = b := fun b => by
    obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_lift (D := D.toPre) (F := C) (ν.eA b)
    obtain ⟨h, hh⟩ := GtValues.exists_val ν g
    exact ⟨h, ν.eA.injective (hh.1.trans hg)⟩
  have main : ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ →
      ν.FamV ϑ (c • N.vth) → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2))
        (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C),
        SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ ν.FamV s f ∧
        (∀ (h : N.Gt) (χ : N.X), f (q.1.1.toAdd + m • χ) h.b * h.s (q.1.1.toAdd + m • χ) = c * N.evT m q h χ) ∧
        ∀ β, (∀ χ, β ≠ q.1.1.toAdd + m • χ) → ∀ x, f β x = 0 := by
    intro th ϑ c hth hϑ
    obtain ⟨⟨_, _⟩, ⟨α, s₁, -, hα, hαn, hs₁, -⟩, -⟩ :=
      GlobalTheory.existsUnique_thetaConst hL V A C ρ hN.2.1 m hm th 1 (one_pow _)
    have hbij := (expBijF_and_expandsF_lin hL V _ hB D A G hG U).1 C (m ^ 2) hm2 w₀ hN.1
    obtain ⟨σ₁, hσ₁, -⟩ := hbij.1 s₁
    obtain ⟨hv₁, -, -, -, -, hv₂⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν (m ^ 2) hm2
    obtain ⟨f₁, hf₁, -⟩ := hv₁ σ₁
    obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL V _ hB D A G hG U).1 m
    have hsm : ∀ {X : Type} [AddCommGroup X] [Module.Free ℤ X], Function.Injective fun χ : X => m • χ := by
      intro X _ _ a b h
      have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
      exact smul_right_injective _ (Int.natCast_ne_zero.2 hm0) h'
    have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
    have hpull := (PullExp.main hL V _ hB D A G hG U C E hinj (m ^ 2) 1 le_rfl hm2
      (exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _)
      (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ ϑ σ₁ hth hσ₁ hs₁
    rw [hEB] at hpull
    obtain ⟨κ, hκ⟩ := exists_kap (D := D.toPre) hL.1.mulPull m
    have pull : ∀ h : N.Gt, (∀ χ, f₁ (m • χ) h.b * h.s (m • χ) =
        c * N.vt (h ^ m) χ * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ)) ∧ ∀ β, (∀ χ, β ≠ m • χ) → f₁ β h.b = 0 := fun h => by
      obtain ⟨g, hg⟩ := GtValues.exists_pt ν h
      obtain ⟨g', hg'⟩ := GtValues.exists_pt ν (h ^ m)
      have act := (hEact C g g').2 ((isNsmul_val ν m hg hg').2 rfl)
      obtain ⟨W, hW⟩ := (coef_basic V D.toPre C (m ^ 2) g).1
      obtain ⟨w, hw, hwv⟩ := exists_frm_kap (act.1.trans (congrArg _ hEB)) W hW κ hκ.1
      obtain ⟨r₁, r₂⟩ := hpull κ hκ g g' act W w hW hw hwv
      have hJ := good ν y
      have e₁ : val κ g.b.left y ν.J = _ := hg.1 ▸ kap_eq ν hL.1.globalFns hκ y h.b
      have e₂ : vF w (𝟙 (Sp C)) ν.J = vF W (𝟙 (Sp C)) ν.J * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ) :=
        (toStk y).injective ((GtValues.toStk_vF _ _ hJ).trans ((congrArg Units.val (hwv y ν.J hJ)).symm.trans
          (((Units.val_mul _ _).trans (congrArg₂ (· * ·) (GtValues.toStk_vF _ _ hJ).symm (congrArg Units.val e₁))).trans
            (map_mul (toStk y) _ _).symm)))
      refine ⟨fun χ => mul_right_cancel₀ (vF_ne ν W) ?_, fun β hβ => ?_⟩
      · have a := r₁ (ν.eX χ)
        rw [hEh, ← map_nsmul, coef_val ν hf₁ hg hW, coef_theta ν hϑ hg' hw, e₂] at a
        rw [a]; ring
      · have a := r₂ (ν.eX β) (by
          rintro ⟨χ, e⟩
          exact hβ (ν.eX.symm χ) (ν.eX.injective (by rw [map_nsmul, ν.eX.apply_symm_apply, ← hEh, e])))
        rw [coef_val ν hf₁ hg hW] at a
        exact (mul_eq_zero.1 ((mul_eq_zero.1 a).resolve_right (vF_ne ν W))).resolve_right (Units.ne_zero _)
    obtain ⟨⟨_, _⟩, ⟨_, _, θ, -, -, -, hθ, -⟩, -⟩ :=
      GlobalTheory.existsUnique_thetaConst hL V A C ρ hN.2.1 m hm th z (hz w₀ hN.1).1
    obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hLB (translT A.A θ.pt) (translPt A.A θ.pt) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
    obtain ⟨σ, hσ, -⟩ := hbij.1 t
    obtain ⟨f, hf, -⟩ := hv₁ σ
    obtain ⟨w, hw⟩ := (SymFrame.main hL V _ hB D C (m ^ 2) hm.pow p).1
    have hΦ := symLift_acts_as_phi hL V _ hB D A G hG U C (m ^ 2) hm.pow p z hz θ hθ w₀ hN.1 w hw s₁ t σ₁ σ
      hσ₁ hσ ht
    obtain rfl := (hv₂ p q w _ σ₁ σ f₁ f hq hw.1 (txFrame_val ν hL.1 hm.pow hq hw) hf₁ hf).1 hΦ
    have on : ∀ (h : N.Gt) (χ : N.X), N.phi q (N.wQ q) f₁ (q.1.1.toAdd + m • χ) h.b * h.s (q.1.1.toAdd + m • χ) =
        c * N.evT m q h χ := fun h χ => by
      rw [add_comm]
      exact phi_term N m q h f₁ c χ ((pull _).1 χ)
    have off : ∀ β, (∀ χ, β ≠ q.1.1.toAdd + m • χ) → ∀ x, N.phi q (N.wQ q) f₁ β x = 0 := fun β hβ x => by
      obtain ⟨h, hh⟩ := hgt (x * q.1.2.b)
      have a := (pull h).2 (β - q.1.1.toAdd) fun χ e => hβ χ (by rw [← e, add_sub_cancel])
      rw [hh] at a
      rw [NumD.phi, a, mul_zero]
    exact ⟨θ, t, σ, _, hθ, ⟨α, s₁, hα, hαn, hs₁, ht⟩, hσ, hf, on, off⟩
  obtain ⟨Θ, t, s, f, h1, h2, h3, h4, h5, h6⟩ := main th ϑ c hth hϑ
  refine ⟨Θ, t, s, ?_⟩
  by_cases hc : c = 0
  · subst hc
    obtain ⟨th', ϑ', c₀, hc₀, hth', hϑ', -⟩ := exists_theta hL hfam U hN.1 ν
    obtain ⟨-, -, -, f', -, -, -, -, h5', h6'⟩ := main th' ϑ' c₀ hth' hϑ'
    refine ⟨c₀⁻¹ • f', h1, h2, h3, ⟨fun h χ => ?_, fun β hβ x => ?_⟩, ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h5', inv_mul_cancel_left₀ hc₀]
    · rw [Pi.smul_apply, Pi.smul_apply, h6' β hβ x, smul_zero]
    · rw [zero_smul]
      convert h4 using 1
      funext β x
      rw [Pi.zero_apply, Pi.zero_apply]
      by_cases hβ : ∃ χ, β = q.1.1.toAdd + m • χ
      · obtain ⟨χ, rfl⟩ := hβ
        obtain ⟨h, rfl⟩ := hgt x
        have e := h5 h χ
        rw [zero_mul] at e
        exact ((mul_eq_zero.1 e).resolve_right (Units.ne_zero _)).symm
      · push_neg at hβ
        exact (h6 β hβ x).symm
  · refine ⟨c⁻¹ • f, h1, h2, h3, ⟨fun h χ => ?_, fun β hβ x => ?_⟩, ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h5, inv_mul_cancel_left₀ hc]
    · rw [Pi.smul_apply, Pi.smul_apply, h6 β hβ x, smul_zero]
    · rwa [smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabTan

theorem tanBasis_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ X) (x' : Sp T ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ i, IsTanAtG t x (v i)) → (∀ w, IsTanAtG t x w → ∃! cf : Fin n → S, IsCombAtG t x v cf w) → ∃ v' : Fin n → (Sp (DualNumber T) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = spMap (dualMap ψ) ≫ v i) ∧ (∀ i, IsTanAtG t' x' (v' i)) ∧ ∀ w, IsTanAtG t' x' w → ∃! cf : Fin n → T, IsCombAtG t' x' v' cf w := by
  intro E _ _ _ H X X' t t' j m S T _ _ ψ x x' hx n v hv hv'
  have := t.semi.comm
  have := t'.semi.comm
  obtain ⟨k₁, k₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange t ψ x n v hv hv'
  rw [← hx] at k₁ k₂
  have h₁ := isGrpPullback_pullback t'.G x'
  have hc := h₁.comp m.cart
  obtain ⟨a, b⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t (x' ≫ j) _ _ hc
  obtain ⟨-, b'⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t' x' _ _ h₁
  choose u hu using fun i => a _ (k₁ i)
  have hu' : ∀ i, (u i).left ≫ pullback.fst t'.G.hom x' ≫ m.φ = spMap (dualMap ψ) ≫ v i := hu
  have hb := (b n u).2 ⟨fun i => by rw [hu']; exact k₁ i, by rw [funext hu']; exact k₂⟩
  obtain ⟨c₁, c₂⟩ := (b' n u).1 hb
  exact ⟨fun i => (u i).left ≫ pullback.fst t'.G.hom x', fun i => by rw [Category.assoc]; exact hu' i, c₁, c₂⟩

end GlobalTheory.SabTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLinearCombinationIsTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.SecJet.TanComb

variable {R : Type} [CommRing R]

theorem zeroPt_w : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsR R).hom = (𝟙_ (Over (Sp R))).hom := by
  show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← Spec.map_id]
  congr 1

def zeroPt : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) zeroPt_w

variable {G : Over (Sp R)} [GrpObj G]

theorem isTangent_iff (v : epsR R ⟶ G) : IsTangent v ↔ zeroPt ≫ v = 1 := by
  have h1 : (1 : 𝟙_ (Over (Sp R)) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [h1, IsTangent]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    simpa [zeroPt] using h
  · intro h
    simpa [zeroPt] using congrArg (fun q => q.left) h

theorem zeroPt_epsScale (c : R) : zeroPt ≫ epsScale R c = zeroPt := by
  apply Over.OverMorphism.ext
  show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR c) = spMap (TrivSqZeroExt.fstHom R R R).toRingHom
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro r
  simp [epsScaleR]

theorem zeroPt_prod (l : List (epsR R ⟶ G)) (hl : ∀ x ∈ l, zeroPt ≫ x = 1) : zeroPt ≫ l.prod = 1 := by
  induction l with
  | nil =>
    rw [List.prod_nil, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (zeroPt ≫ toUnit _) (toUnit _)]
  | cons a l ih =>
    rw [List.prod_cons, MonObj.comp_mul, hl a (List.mem_cons_self ..), ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)), _root_.mul_one]

end GlobalTheory.SecJet.TanComb

namespace GlobalTheory.SecJet

theorem isTangent_tanComb (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (m : ℕ) (v : Fin m → (epsR R ⟶ G))
    (c : Fin m → R) : (∀ i, IsTangent (v i)) → IsTangent (tanComb c v) := by
  intro hv
  rw [TanComb.isTangent_iff, tanComb]
  refine TanComb.zeroPt_prod _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  rw [← Category.assoc, TanComb.zeroPt_epsScale, ← TanComb.isTangent_iff]
  exact hv i

end GlobalTheory.SecJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.TransLift

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem lift_isTranslate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ X) (x' : Sp R' ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (u : Sp (DualNumber R) ⟶ t.G.left) (u' : Sp (DualNumber R') ⟶ t'.G.left), IsTanAtG t x u → IsTanAtG t' x' u' → u' ≫ m.φ = spMap (dualMap ψ) ≫ u → ∀ (S : Type) [CommRing S] (φS : R' →+* S) (g₀' : Sp S ⟶ t'.G.left), g₀' ≫ t'.G.hom = spMap φS ≫ x' → ∀ w : Sp (DualNumber S) ⟶ t.G.left, IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u w → ∃ w' : Sp (DualNumber S) ⟶ t'.G.left, w' ≫ m.φ = w ∧ IsTranslate t' φS g₀' u' w' := by
  intro E _ _ _ H X X' t t' j m R R' _ _ ψ x x' hx u u' hu hu' huu S _ φS g₀' hg₀' w hw
  obtain ⟨w', hw', -⟩ := existsUnique_isTranslate t' φS hg₀' hu'
  refine ⟨w', ?_, hw'⟩
  have hsq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  have hg : (g₀' ≫ m.φ) ≫ t.G.hom = spMap (φS.comp ψ) ≫ x := by
    rw [Category.assoc, hsq, ← Category.assoc, hg₀', Category.assoc, hx, ← Category.assoc, spMap_comp'']
  obtain ⟨g', v', h₁, h₂, h₃⟩ := hw'
  have ht : IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u (w' ≫ m.φ) := by
    let T : Over X' := tEpsG (g₀' ≫ t'.G.hom)
    have heq : (tEpsG ((g₀' ≫ m.φ) ≫ t.G.hom)).hom = T.hom ≫ j := by
      show spMap _ ≫ (g₀' ≫ m.φ) ≫ t.G.hom = (spMap _ ≫ g₀' ≫ t'.G.hom) ≫ j
      rw [Category.assoc, Category.assoc, Category.assoc, hsq]
    let e : tEpsG ((g₀' ≫ m.φ) ≫ t.G.hom) ⟶ Over.mk (T.hom ≫ j) :=
      Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact heq.symm)
    refine ⟨e ≫ pushHom m.cart T g', e ≫ pushHom m.cart T v', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ g'.left ≫ m.φ = _
      rw [Category.id_comp, h₁, Category.assoc]
    · show 𝟙 _ ≫ v'.left ≫ m.φ = _
      rw [Category.id_comp, h₂, Category.assoc, huu, ← Category.assoc, spMap_comp'', dualMap_comp'']
    · rw [← MonObj.comp_mul, ← map_mul]
      show 𝟙 _ ≫ (g' * v').left ≫ m.φ = _
      rw [Category.id_comp, h₃]
  exact (existsUnique_isTranslate t (φS.comp ψ) hg hu).unique ht hw

end GlobalTheory.TransLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermIdeal
section
noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.ConeMono

variable {X : Type} [AddCommGroup X]

def ev (a b : X) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := LinearMap.applyₗ b ∘ₗ LinearMap.applyₗ a

@[simp] theorem ev_apply (a b : X) (β : LinearMap.BilinForm ℤ X) : ev a b β = β a b := rfl

def expo (n : X × X →₀ ℤ) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := n.sum fun p k => k • ev p.1 p.2

def mono {K : Type} [Field K] (q : X → X → Kˣ) (n : X × X →₀ ℤ) : Kˣ := n.prod fun p k => q p.1 p.2 ^ k

def termIdeal [Module.Finite ℤ X] (V : Type) [CommRing V] {K : Type} [Field K] [Algebra V K] (φ : InvFun ℤ) (d : ℕ) (q : X → X → Kˣ) :
    Ideal V :=
  Ideal.span {v | ∃ n : X × X →₀ ℤ, (∀ β ∈ balForms (id : ℤ → ℤ) X, (∀ y, 0 ≤ β y y) →
      (d : ℝ) * φ.evalZ β ≤ (expo n β : ℝ)) ∧ algebraMap V K v = (mono q n : K)}

end GlobalTheory.ConeMono
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegreeStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : Weight Dw) (n : ℕ) (b : ℝ), 1 ≤ Dw.p → Even n → (∀ τ, Antitone (u τ)) → (∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j) → (∀ τ i, |(u τ i : ℝ)| ≤ b) → Dom (thA Dw u n) n ∧ wtZ (thA Dw u n) n = wtOf Dw (u + parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧ LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧ (DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := by
  first | exact @GlobalTheory.RefSum.thA_dominant_lastPos_degree | exact GlobalTheory.RefSum.thA_dominant_lastPos_degree | (intros; apply GlobalTheory.RefSum.thA_dominant_lastPos_degree <;> assumption)
end

