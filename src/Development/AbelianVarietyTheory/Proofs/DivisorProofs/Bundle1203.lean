import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineBundleDescendsToCountableSubfield
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ProjCountableDescent

open GlobalTheory.PolCountableDescent in

theorem projLB_descends_to_countable_subfield : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∀ (L : LB X), L.IsLB → ∃ (K₁ : Subfield K) (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (ψ : X ⟶ X₁) (L₁ : LB X₁), Countable K₁ ∧ IsProjOver p₁ ∧ IsPullback ψ p p₁ (spMap (algebraMap K₁ K)) ∧ L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  intro K _ X p hp L hL
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ X p hp
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ X p₀ p φ L hL sq
  let s : Finset K := s₀ ∪ s₂
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  have sq₁ : IsPullback (pullback.fst p₀ inc) (pullback.snd p₀ inc) p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : X ⟶ pullback p₀ inc := sq₁.lift φ (p ≫ spMap K₁.subtype)
    (by rw [Category.assoc, spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ pullback.fst p₀ inc = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd p₀ inc = p ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨L₁, hL₁, hI⟩ := H₂ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) _ _ _ ψ
    sq₁ hψ₁ hψ₂
  refine ⟨K₁, _, pullback.snd p₀ inc, ψ, L₁, countable_closure s,
    ProjSpace.isProjOver_pullback_snd _ hp₀, ?_, hL₁, hI⟩
  refine IsPullback.of_right (t := sq₁) ?_ hψ₂
  have e : spMap (algebraMap K₁ K) ≫ inc = spMap K₀.subtype := spMap_subtype_comp h
  rw [hψ₁, e]
  exact sq

end GlobalTheory.ProjCountableDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceIntegralSmoothProjectiveDimStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveSpace_integral_smooth_projective_dim : ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PSpace k N) ∧ topologicalKrullDim (PSpace k N) = N ∧ IsProjOver (PSpace.str k N) ∧ SmoothOfRelativeDimension N (PSpace.str k N) := by
  first | exact @GlobalTheory.pspace_integral_dim_proj_smooth | exact GlobalTheory.pspace_integral_dim_proj_smooth | (intros; apply GlobalTheory.pspace_integral_dim_proj_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
section
open GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.ShapeSmoothFinite

theorem continuous_matCoord_ujMat {n : ℕ} (ε : Fin n → Bool) : Continuous (matCoord (ujMat ε)) :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val

theorem mem_ccMat_and_isBiFinite {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : Mat n → ℂ) (hφ : φ ∈ ShapeM ε d) :
    (fun g : UJ ε => φ (toM g)) ∈ CcMat (ujMat ε) ∧ IsBiFinite (KG ε) (fun g : UJ ε => φ (toM g)) := by
  obtain ⟨h0, hadd, hsmul⟩ := GlobalTheory.isBiFinite_subspace (UJ ε) (KG ε)
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, ⟨hH, R, hR⟩, -, rfl⟩ := h
    exact ⟨GlobalTheory.CutoffPoly.cutoff_mul_poly_mem_ccMat n ε H R hH hR P, GlobalTheory.PolyShapeFinite.main n ε H P⟩
  | zero => exact ⟨Submodule.zero_mem _, h0⟩
  | add φ ψ _ _ h h' => exact ⟨Submodule.add_mem _ h.1 h'.1, hadd _ _ h.2 h'.2⟩
  | smul c φ _ h => exact ⟨Submodule.smul_mem _ c h.1, hsmul c _ h.2⟩

theorem stShape : GlobalTheory.PsCo.Pc1.StShape := by
  intro n ε d φ hφ
  obtain ⟨h1, h2⟩ := mem_ccMat_and_isBiFinite ε d φ hφ
  exact ⟨h1, h2, continuous_of_mem_ccSmooth (continuous_matCoord_ujMat ε) h1, (mem_ccSmooth.1 h1).1⟩

end GlobalTheory.ShapeSmoothFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutLinPack
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

theorem put_lin_pack : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), (∀ X Y : Matrix (Fin p) (Fin q) R, put n o₁ o₂ (X + Y) = put n o₁ o₂ X + put n o₁ o₂ Y) ∧ (∀ X : Matrix (Fin p) (Fin q) R, put n o₁ o₂ (-X) = -put n o₁ o₂ X) ∧ put n o₁ o₂ (0 : Matrix (Fin p) (Fin q) R) = 0 ∧ (∀ X : Matrix (Fin p) (Fin q) R, (put n o₁ o₂ X)ᵀ = put n o₂ o₁ Xᵀ) ∧ eye R n o₁ o₂ (p + q) = eye R n o₁ o₂ p + eye R n (o₁ + p) (o₂ + p) q ∧ eye R n 0 0 n = 1 ∧ (∀ X : Matrix (Fin p) (Fin q) R, (p = 0 ∨ q = 0) → put n o₁ o₂ X = 0) ∧ (∀ X : Matrix (Fin n) (Fin n) R, put n 0 0 X = X) := by
  intro R _ n o₁ o₂ p q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y
    ext i j
    simp only [put, Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  · intro X
    ext i j
    simp only [put, Matrix.of_apply, Matrix.neg_apply]
    split_ifs <;> simp
  · ext i j
    simp only [put, Matrix.of_apply, Matrix.zero_apply]
    split_ifs <;> simp
  · intro X
    ext i j
    simp only [put, Matrix.of_apply, Matrix.transpose_apply]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨h1.2, h1.1⟩ h2
    · exact absurd ⟨h2.2, h2.1⟩ h1
    · rfl
  · ext i j
    simp only [eye, put, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · ext i j
    simp only [eye, put, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega | (exfalso; omega) | simp_all
  · intro X h
    ext i j
    simp only [put, Matrix.of_apply, Matrix.zero_apply]
    split_ifs with h1
    · exfalso; omega
    · rfl
  · intro X
    ext i j
    simp only [put, Matrix.of_apply]
    split_ifs with h1
    · simp
    · exfalso; omega

end GlobalTheory.GamMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutMulPut
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

private theorem put_apply' {R : Type} [CommRing R] (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R)
    (i j : Fin n) : put n o₁ o₂ X i j =
      if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
        X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0 := rfl

theorem put_mul_put :
    ∀ (R : Type) [CommRing R] (n o₁ o₂ o₃ o₄ p q s t : ℕ) (X : Matrix (Fin p) (Fin q) R)
      (Y : Matrix (Fin q) (Fin s) R) (Z : Matrix (Fin t) (Fin s) R),
      (o₂ + q ≤ n → put n o₁ o₂ X * put n o₂ o₃ Y = put n o₁ o₃ (X * Y)) ∧
      ((o₂ + q ≤ o₃ ∨ o₃ + t ≤ o₂) → put n o₁ o₂ X * put n o₃ o₄ Z = 0) := by
  intro R _ n o₁ o₂ o₃ o₄ p q s t X Y Z
  refine ⟨fun hn => ?_, fun hd => ?_⟩
  · ext i j
    rw [Matrix.mul_apply, put_apply']
    let e : Fin q ↪ Fin n := ⟨fun c => ⟨o₂ + c.val, by omega⟩, fun a b h => by
      simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩
    have he : ∀ c : Fin q, (e c).val = o₂ + c.val := fun c => rfl
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) ?_, Finset.sum_map]
    · by_cases hi : o₁ ≤ i.val ∧ i.val < o₁ + p
      · by_cases hj : o₃ ≤ j.val ∧ j.val < o₃ + s
        · rw [dif_pos ⟨hi, hj⟩, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun c _ => ?_
          have hc : (o₂ ≤ (e c).val ∧ (e c).val < o₂ + q) := by rw [he]; omega
          rw [put_apply', put_apply', dif_pos ⟨hi, hc⟩, dif_pos ⟨hc, hj⟩]
          have h1 : (⟨(e c).val - o₂, by omega⟩ : Fin q) = c := Fin.ext (by show (e c).val - o₂ = c.val; rw [he]; omega)
          rw [h1]
        · rw [dif_neg (fun h => hj h.2)]
          refine Finset.sum_eq_zero fun c _ => ?_
          rw [put_apply' n o₂ o₃ Y, dif_neg (fun h => hj h.2), mul_zero]
      · rw [dif_neg (fun h => hi h.1)]
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [put_apply' n o₁ o₂ X, dif_neg (fun h => hi h.1), zero_mul]
    · intro l _ hl
      have : ¬ (o₂ ≤ l.val ∧ l.val < o₂ + q) := by
        rintro ⟨h1, h2⟩
        apply hl
        refine Finset.mem_map.2 ⟨⟨l.val - o₂, by omega⟩, Finset.mem_univ _, ?_⟩
        exact Fin.ext (by show o₂ + (l.val - o₂) = l.val; omega)
      rw [put_apply' n o₁ o₂ X, dif_neg (fun h => this h.2), zero_mul]
  · ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : o₂ ≤ l.val ∧ l.val < o₂ + q
    · rw [put_apply' n o₃ o₄ Z, dif_neg (fun h => by omega), mul_zero]
    · rw [put_apply' n o₁ o₂ X, dif_neg (fun h => h1 h.2), zero_mul]

end GlobalTheory.GamMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QWeilZeroCartier
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PairStep

theorem qWeil_zero_cartier {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ) :
    qWeil (0 : CartierDiv X) m = 0 := by
  funext z
  have : (0 : CartierDiv X).mult z = 0 := by
    rw [(CartierDiv.isEqn_zero z).mult_eq]
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  simp [qWeil, this]

theorem qNum_zero_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ N : LB X, QNum p N 0 0 := by
  intro X _ _ p _ N
  letI := algebraΓOfHom p
  refine ⟨1, 0, one_pos, CartierDiv.eff_zero, (qWeil_zero_cartier 1).symm, fun C _ => ?_⟩
  rw [interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]
  simp

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WType

theorem range_w0C_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.toRealDat.LUnif → ∀ i, LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ⊓ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hU i
  obtain ⟨hC, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hI := (GlobalTheory.T.goodProjector_unitaryFormsModel_laws R.toRealDat F.lv2 hC hX i).1
  have hs : ∀ a, cj (twAt D.what₂.embLL A3.A.v0) (A3.A.fam.v0.embedding a) = sg0 D A3.A a := fun a => by
    show cj _ (A3.A.v0.embedding a) = _
    rw [emb_eq D.what₂.embLL A3.A.v0 a, cj_cj]
  rw [GlobalTheory.T.range_complex_points_level_forms_eq_good_forms R F hOk hW hU false i]
  ext x
  have hw := GlobalTheory.WatType.wat_iff_type R.toRealDat F.lv2 hOk.ok2 hC false i (Tw.out x)
  have hL : x ∈ Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) ↔ (R.HW i (sg0 D A3.A)).e (Tw.out x) ∈ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := Iff.rfl
  have hR : Tw.out x ∈ LinearMap.range (eH R.toRealDat i) ↔ eH R.toRealDat i (Tw.out x) = Tw.out x := by
    refine ⟨?_, fun h => ⟨_, h⟩⟩
    rintro ⟨y, hy⟩
    rw [← hy, ← Module.End.mul_apply, hI]
  have hT : x ∈ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ ↔ ∀ p : (F.lv2.lvl false).P, R.gW i (sg0 D A3.A) (p : G) (Tw.out x) = sg0 D A3.A ((((F.lv2.lvl false).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • Tw.out x := by
    unfold typeSubspace
    refine (Submodule.mem_iInf (R := ℂ) (M := (R.toCx3 F).W i) _).trans (forall_congr' fun p => ?_)
    show R.gW i (sg0 D A3.A) (p : G) (Tw.out x) - cj (twAt D.what₂.embLL A3.A.v0) (A3.A.fam.v0.embedding ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL)) • Tw.out x = 0 ↔ _
    rw [sub_eq_zero, hs]
    rfl
  constructor
  · intro h
    rw [hL, hw] at h
    exact ⟨hR.2 h.1, hT.2 h.2⟩
  · intro h
    rw [hL, hw]
    exact ⟨hR.1 h.1, hT.1 h.2⟩

end GlobalTheory.WType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankResidueBasisMatrixSuccOfAdjoinVector
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

theorem rank_residue_succ_of_adjoin
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (Ac As : Matrix (Fin n) (Fin n) O) (x : Fin n → O) :
    Irreducible ϖ → (∀ y : Fin n → O, ∃ u, Ac *ᵥ u = fun a => ϖ * y a) →
    (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) →
    (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (¬ ∃ u, Ac *ᵥ u = x) →
    (As.map (residue O)).rank = (Ac.map (residue O)).rank + 1 := by
  intro hϖ h1 h2 h3 h4 h5
  set bar := residue O with hbar
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O),
      (A.map bar) *ᵥ (bar ∘ v) = bar ∘ (A *ᵥ v) := by
    intro A v; funext i; exact (RingHom.map_mulVec bar A v i).symm
  have hlift : ∀ z : Fin n → ResidueField O, ∃ v : Fin n → O, bar ∘ v = z := by
    intro z
    refine ⟨fun i => (residue_surjective (z i)).choose, ?_⟩
    funext i; exact (residue_surjective (z i)).choose_spec
  set V := LinearMap.range (As.map bar).mulVecLin
  set Wc := LinearMap.range (Ac.map bar).mulVecLin
  set xb : Fin n → ResidueField O := bar ∘ x
  have hV : V = Wc ⊔ Submodule.span (ResidueField O) {xb} := by
    apply le_antisymm
    · rintro v ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := hlift z
      obtain ⟨u, c, hc⟩ := h2 w
      rw [Matrix.mulVecLin_apply, hmap, hc]
      have : bar ∘ (Ac *ᵥ u + fun a => c * x a) = (Ac.map bar) *ᵥ (bar ∘ u) + bar c • xb := by
        rw [hmap]; funext i; simp [xb]
      rw [this]
      exact Submodule.add_mem_sup ⟨bar ∘ u, rfl⟩
        (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    · apply sup_le
      · rintro v ⟨z, rfl⟩
        obtain ⟨u, rfl⟩ := hlift z
        obtain ⟨w, hw⟩ := h4 u
        refine ⟨bar ∘ w, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hmap, hmap, hw]
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        obtain ⟨w, hw⟩ := h3
        exact ⟨bar ∘ w, by rw [Matrix.mulVecLin_apply, hmap, hw]⟩
  have hxb : xb ∉ Wc := by
    rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := hlift z
    rw [Matrix.mulVecLin_apply, hmap] at hz
    have hmem : ∀ a, (x - Ac *ᵥ u) a ∈ Ideal.span {ϖ} := by
      intro a
      rw [← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
      have := congrFun hz a
      simp only [Function.comp_apply, xb] at this
      rw [Pi.sub_apply, map_sub, ← hbar, this, sub_self]
    choose y hy using fun a => Ideal.mem_span_singleton'.1 (hmem a)
    obtain ⟨u', hu'⟩ := h1 y
    apply h5
    refine ⟨u + u', ?_⟩
    rw [Matrix.mulVec_add, hu']
    funext a
    have := hy a
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply]
    rw [mul_comm, this]; ring
  have hxb0 : xb ≠ 0 := by
    intro h; exact hxb (h ▸ Wc.zero_mem)
  have hinf : Wc ⊓ Submodule.span (ResidueField O) {xb} = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvW, hvs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvs
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using Wc.smul_mem c⁻¹ hvW) hxb
  have key := Submodule.finrank_sup_add_finrank_inf_eq Wc (Submodule.span (ResidueField O) {xb})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hxb0, ← hV] at key
  show Module.finrank _ V = Module.finrank _ Wc + 1
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHomHermitianTraceFormSelfEqFrameNormSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HRatFrame

theorem trace_conjTranspose_mul_self_sum {R : Type*} [CommRing R] [StarRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) :
    Matrix.trace (Aᴴ * A) = ∑ a, ∑ b, star (A a b) * A a b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

theorem hRat_frame : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.LatVac.hRat S T v v = ∑ a, ∑ b, star (((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) a b) * ((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) a b := by
  intro D S T frS frT hS hT v
  have hT2 : frT.1 * (frT⁻¹ : GL (Fin T.rank) D.host.E).1 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hS2 : frS.1 * (frS⁻¹ : GL (Fin S.rank) D.host.E).1 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hv : frT.1 * ((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) * (frS⁻¹ : GL (Fin S.rank) D.host.E).1 = v := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hS2, Matrix.mul_one, ← Matrix.mul_assoc, hT2, Matrix.one_mul]
  have key := GlobalTheory.SemicharTrace.hRat_frames S T frS frT hS hT ((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1)
  rw [hv] at key
  rw [key, trace_conjTranspose_mul_self_sum]

end GlobalTheory.HRatFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLatticeSelfDualFgFullIndexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_lattice_selfDual_fg_full_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → SelfDual (gamQ ψ S T) (latQ S T ΛS ΛT) ∧ (latQ S T ΛS ΛT).toAddSubgroup.FG ∧ (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • x ∈ latQ S T ΛS ΛT) ∧ ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) = (latQ S T ΛS ΛT).toAddSubgroup.relIndex ((latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom) := by
  first | exact @GlobalTheory.RatLattice.latQ_selfDual_fg_full_index | exact GlobalTheory.RatLattice.latQ_selfDual_fg_full_index | (intros; apply GlobalTheory.RatLattice.latQ_selfDual_fg_full_index <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpaStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    IsTopologicalAddGroup (WOF F E nS nT) ∧ LocallyCompactSpace (WOF F E nS nT) ∧
    SecondCountableTopology (WOF F E nS nT) ∧ T2Space (WOF F E nS nT) ∧ DiscreteTopology (ratLF F E nS nT) ∧
    ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  first | exact @GlobalTheory.AdelicMatrixLatticeF.lattice | exact GlobalTheory.AdelicMatrixLatticeF.lattice | (intros; apply GlobalTheory.AdelicMatrixLatticeF.lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoint_finitePart_isotropic_pairing : ∀ {D : D7} (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E), symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 := by
  first | exact @GlobalTheory.RatFinIso.isotropic | exact GlobalTheory.RatFinIso.isotropic | (intros; apply GlobalTheory.RatFinIso.isotropic <;> assumption)
end

