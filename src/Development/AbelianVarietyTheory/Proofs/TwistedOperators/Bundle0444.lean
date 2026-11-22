import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesDifferByIsometryAndTriangularOfPeriods
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralScalarOfPulledBackGeneratorExtendsModel
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0411
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0405
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramesDifferByIsometryOfTriangularPeriods
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix ComplexConjugate

noncomputable section

namespace GlobalTheory.PeriodBorelQ

open GlobalTheory.FramePeriod GlobalTheory.PeriodBorel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem natPer_move_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a) (τ : E →+* ℂ) (q : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) (n : ℕ) :
    natPer τ X'.Gm q ((a : Matrix (Fin r) (Fin r) E).map τ * M)
      (Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v)) n = natPer τ X.Gm q M (Data.emb τ v) n := by
  have he : Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ Data.emb τ v := by
    funext k; simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).map τ
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · exact h.hermC_eq τ (col M ⟨n, hn⟩) _
    · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
  · rfl

theorem natPer_natCast_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (N : ℕ) (v : Fin r → E) (n : ℕ) :
    natPer τ G q M (Data.emb τ ((N : E) • v)) n = (N : ℂ) * natPer τ G q M (Data.emb τ v) n := by
  have he : Data.emb τ ((N : E) • v) = (N : ℂ) • Data.emb τ v := by
    funext k; simp [Data.emb]
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · rw [FD.hermC_smul_right, Complex.conj_natCast]
    · rw [Matrix.mulVec_smul]; rfl
  · simp

theorem borel_of_periods_q : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (h : QMatch X X' N a), 0 < N → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * Formalism.L2.PjFree.perFr X x v τ j) → ∃ b ∈ Bor X'.Ψ r, x' = rmul (lact a (castFr h.psi x)) b ∧ (IsUnitFr X x → IsUnitFr X' x' → (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ τ, ∀ i < m τ, ‖A τ i i‖ = 1) := by
  intro E _ _ _ r X X' N a h hN0 m hm1 hm2 x hx x' hx' A hA hper
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have hz := h.mem_dom hx
  set z := lact a (castFr h.psi x) with hzd
  have hlat : ∀ w ∈ X'.Λ, ∃ v ∈ X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ v = (N : E) • w := by
    intro w hw
    refine ⟨_, h.lat' w hw, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hloc := fun τ : X'.Ψ => loc_borel X' τ.1 (mat z τ) (mat x' τ) (hz τ).1 (hx' τ).1 (A τ.1) (A (conjEmb τ.1))
    (hA _) (hA _)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm1 τ.1 (h.mem τ)
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_mem X' x' _ τ.1 τ.2, hper τ.1 i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [perFr_mem X x v τ.1 (h.mem τ), ← natPer_move_q h, h.p0, hav, natPer_natCast_smul, mul_left_comm]
      rfl)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm2 _ (conjEmb_not_mem X (h.mem τ))
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_conj X' x' _ τ.1 τ.2 i hi, hper _ i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [perFr_conj X x v τ.1 (h.mem τ) j (h.p0 ▸ Finset.mem_range.1 hj), ← natPer_move_q h, h.p0, hav,
        natPer_natCast_smul, mul_left_comm]
      rfl)
  let b : Frame X'.Ψ r := fun τ => ((mat z τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ)
  have hb : b ∈ Bor X'.Ψ r := fun τ => by
    refine ⟨?_, (hloc τ).1⟩
    show ((mat z τ)⁻¹ * mat x' τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hz τ).1) (hx' τ).1
  have hxb : x' = rmul z b := by
    funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (mat z τ) (mat x' τ) (isUnit_iff_ne_zero.2 (hz τ).1)).symm
  refine ⟨b, hb, hxb, fun hu hu' => ?_⟩
  have hbd : ∀ τ i, ‖b τ i i‖ = 1 := by
    intro τ i
    have e := FrameDegreeData.ratio_rmul X' z hz hb τ i
    rw [← hxb, norm_div, norm_div, hu', hu', hzd, h.dmin_eq, h.dmin_eq, hu, hu, div_one, _root_.mul_one] at e
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e.symm
  refine ⟨hbd, fun τ i hi => ?_⟩
  by_cases hτ : τ ∈ X.Ψ
  · rw [hm1 τ hτ, h.p0] at hi
    exact ((hloc ⟨τ, h.psi ▸ hτ⟩).2 (hbd _)).1 i hi
  · rw [hm2 τ hτ, h.p0] at hi
    have := ((hloc ⟨conjEmb τ, h.psi ▸ conjEmb_mem X hτ⟩).2 (hbd _)).2 i hi
    rwa [conjEmb_conjEmb] at this

end GlobalTheory.PeriodBorelQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem conjRead_holds : ConjRead := GlobalTheory.Asc.FamilyModel.conjRead

end GlobalTheory.Asc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeElementKeepsOneSubIdempotentPartLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeOffParts
open scoped Matrix

theorem mulVec_one_sub_idempotent_of_split_sum_identity {A : Type} [CommRing A] {n : ℕ} (a b : A) (h1 : a * a = a) (h2 : a * b = 0)
    (M : Matrix (Fin n) (Fin n) A) (z : Fin n → A) (h6 : M *ᵥ z = (a + b) • M *ᵥ z + z - (a + b) • z) :
    M *ᵥ ((1 - a) • z) = b • M *ᵥ z + z - a • z - b • z := by
  have hP : (1 - a) * (a + b) = b := by linear_combination -h1 - h2
  rw [Matrix.mulVec_smul]
  conv_lhs => rw [h6]
  rw [smul_sub, smul_add, smul_smul, smul_smul, hP, sub_smul, one_smul]
  abel

open GlobalTheory.SplitPlace in
theorem inv_part_mem {D : D7} {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {ϖ : D.host.E} {k : ℕ} {a₀ : GA D V}
    (ha : Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀) :
    ∀ z ∈ Formalism.L2.NTheta.LamHat V,
      fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z) ∈ Formalism.L2.NTheta.LamHat V := by
  intro z hz
  obtain ⟨-, hs, h3, -⟩ := ha
  have hi := idem_mem he.1
  have hci := cf_mem hi
  have h3' : ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D e • fm V a₀ *ᵥ y ∈ Formalism.L2.NTheta.LamHat V := h3
  have hadj := adj_mem V (finPart D e) a₀ h3' z hz
  have h6 := mulVec_parts (finPart D) ((suppAt_iff e V a₀⁻¹).1 (suppAt_inv hs)) z
  rw [RingHom.map_add, fin_cA, ← fm_eq] at h6
  have e1 : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have e2 : finPart D e * cf D (finPart D e) = 0 := by rw [← fin_cA, ← map_mul, he.2.1, map_zero]
  rw [mulVec_one_sub_idempotent_of_split_sum_identity _ _ e1 e2 _ z h6]
  have m1 : finPart D e • z ∈ Formalism.L2.NTheta.LamHat V := smul_mem V hi hz
  have m2 : cf D (finPart D e) • z ∈ Formalism.L2.NTheta.LamHat V := smul_mem V hci hz
  have m3 := (Formalism.L2.NTheta.LamHat V).add_mem hadj hz
  have m4 := (Formalism.L2.NTheta.LamHat V).sub_mem m3 m1
  exact (Formalism.L2.NTheta.LamHat V).sub_mem m4 m2

open GlobalTheory.SplitPlace in
theorem hat_one_mem {D : D7} {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {ϖ : D.host.E} {k : ℕ} {a₀ : GA D V}
    (ha : Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀) :
    ∀ w ∈ latGHat V 1, fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • w) ∈ latGHat V 1 := by
  intro w hw
  let f : (Fin V.rank → RF D) →+ (Fin V.rank → RF D) :=
    (Matrix.mulVecLin (fm V a₀⁻¹)).toAddMonoidHom.comp (DistribMulAction.toAddMonoidHom _ (1 - finPart D e))
  change f w ∈ latGHat V 1
  unfold latGHat at hw ⊢
  refine AddSubgroup.mem_comap.1 ((AddSubgroup.closure_le (K := AddSubgroup.comap f _)).2 ?_ hw)
  rintro _ ⟨a, haA, x, ⟨x', hx', rfl⟩, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  refine AddSubgroup.subset_closure ⟨a, haA, _, ⟨fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • x'), ?_, rfl⟩, ?_⟩
  · have hx'' : x' ∈ Formalism.L2.NTheta.LamHat V := by
      rw [← GlobalTheory.LatReflection.latHat_eq_lamHat]; exact hx'
    have := inv_part_mem he ha x' hx''
    rw [← GlobalTheory.LatReflection.latHat_eq_lamHat] at this
    exact this
  · simp only [map_one, Units.val_one, Matrix.one_mulVec]
    change fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • (((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) • x')) =
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) • (fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • x'))
    rw [smul_comm (1 - finPart D e), Matrix.mulVec_smul]

open GlobalTheory.SplitPlace in
theorem off_parts : ∀ (D : D7) (V : HSp D) (e : AE D) (ϖ : D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.Theta.IsSplitIdem D e → Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀ →
    ∀ y ∈ latGHat V g, (1 - finPart D e) • y ∈ latGHat V (g * a₀) := by
  intro D V e ϖ k g a₀ he ha y hy
  obtain ⟨z, hz, rfl⟩ := ((GlobalTheory.MarkCoset.latG_spec D V g).2 y).1 hy
  refine ((GlobalTheory.MarkCoset.latG_spec D V (g * a₀)).2 _).2
    ⟨fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z), hat_one_mem he ha z hz, ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  change (finHom V g).1 *ᵥ (fm V a₀ *ᵥ (fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z))) = _
  rw [fm_vec_inv, Matrix.mulVec_smul]

end GlobalTheory.HeckeOffParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingFormsStatement
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_lifts_to_lattice_map_scaling_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → IsHkIsog p (F.u i P) (F.u j P') C ψ ψp → ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ ∀ z, F.ex j P' (h z) = ψp (F.ex i P z) := by
  first | exact @GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog | exact GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog | (intros; apply GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignatureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D := by
  first | exact @GlobalTheory.RationalIsometry.rationalSt | exact GlobalTheory.RationalIsometry.rationalSt | (intros; apply GlobalTheory.RationalIsometry.rationalSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

namespace GlobalTheory.Tow

theorem idemAt_orth {D : D7} {P Q : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b Q) (h : P ≠ Q) : a * b = 0 := by

  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have ha0 := GlobalTheory.PlaceModelSum.infPart_split ha.1
  have hda := (GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 ha0 P).mp ha.2
  have hdb := (GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) Q).mp hb.2
  apply hΦ.ext'
  · rw [map_mul, ha0, zero_mul, map_zero]
  · intro R
    rw [GlobalTheory.IdemSupport.ev_mul, GlobalTheory.IdemSupport.ev_zero]
    by_cases hR : R = P
    · rw [hR, hdb.2.2 P h, mul_zero]
    · rw [hda.2.2 R hR, zero_mul]

theorem idemAt_unique {D : D7} {P : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b P) : a = b := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  exact GlobalTheory.IdemSupport.delta_unique hΦ
    ((GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 (GlobalTheory.PlaceModelSum.infPart_split ha.1) P).mp ha.2)
    ((GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) P).mp hb.2)

theorem idemSum_mul_of_subset {D : D7} {e e₂ : AE D} {P P₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsIdemSum e P) (h₂ : IsIdemSum e₂ P₂) (hP : P ⊆ P₂) : e₂ * e = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨fs, hfs, rfl⟩, -⟩ := h₂
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_

  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem R (hP hR)]
  · rw [idemAt_unique (hfs R (hP hR)) (hes R hR)]
    exact (hes R hR).1.1
  · intro Q hQ hQR
    exact idemAt_orth (hfs Q hQ) (hes R hR) hQR

end GlobalTheory.Tow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem suppPl_emb {D : D7} (V : HSp D) (v : FinPl D) (k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.WeilParts.SuppPl (pairA D.host.F 0 (singleV D.host.F v 1)) V (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k) := by
  intro i j
  let t₁ := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := D.host.E) (R' := AF D.host.F)
    (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl)
  let t₂ := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := D.host.E) (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v)
  have key : ∀ x, t₁ (t₂ 1) * t₁ (t₂ x) = t₁ (t₂ x) := fun x => by rw [← map_mul, ← map_mul, one_mul]
  change t₁ (t₂ 1) * (((1 - t₁ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      t₁ ((1 - t₂ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j + t₂ ((HA.mat _ _ _ k).1 i j))) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
    ((1 - t₁ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      t₁ ((1 - t₂ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j + t₂ ((HA.mat _ _ _ k).1 i j))) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j
  by_cases e : i = j
  · subst e
    simp only [Matrix.one_apply_eq, mul_one, map_add, map_sub]
    linear_combination key ((HA.mat _ _ _ k).1 i i) - key 1
  · simp only [Matrix.one_apply_ne e, mul_zero, zero_add, sub_zero]
    exact key _

theorem emb_keeps_latHat {D : D7} (V : HSp D) {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hL : L.FG)
    (v : FinPl D) {k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v} (hk : k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram L v) (y) :
    y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k)).mulVec y ∈
        latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) := by
  have h := GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  rw [GlobalTheory.AdelicU.levelOff_eq] at h
  exact (GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ hL _).1 h.2 y

theorem inertVacuumFixed : ∀ D : D7, InertVacuumFixed D := by
  intro D ψ S T χS χT om ΛS ΛT hW hS hT v hv uS uT f hf hvac k hk k' hk'
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hns : GlobalTheory.WeilParts.NonSplitAt D v (pairA D.host.F 0 (singleV D.host.F v 1)) := ⟨hε, hv⟩
  refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om ((GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩)
     hW v _ hns uS uT _ _
    (suppPl_emb S v k) (suppPl_emb T v k')
    (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T ΛS ΛT hS hT v _ hε _ _
      (emb_keeps_latHat S hS.1.fg v hk) (emb_keeps_latHat T hT.1.fg v hk')) f hf fun u hu => ?_
  obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hns
  have h1 : 2 • (a • u) = u := by
    rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
  have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
  rwa [h1] at h2

end GlobalTheory.PlaceTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignatureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrameExtension_of_rank_zero_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.p + Dw.q = 0 → IntFrExt Xo c := by
  first | exact @GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero | exact GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero | (intros; apply GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralScalarOfPulledBackGeneratorExtendsModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (N M : ℕ) (a : T.Fr) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F' ≫ F = 𝟙 _ ^ N → IsUnit (N : T.V) → letI := io.toAlgebra; IsPullOf M f a y'.1.s t → Reg I M t → a ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.HkIntegral.PullScalar.mem_range_of_reg | exact GlobalTheory.HkIntegral.PullScalar.mem_range_of_reg | (intros; apply GlobalTheory.HkIntegral.PullScalar.mem_range_of_reg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonneg
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

namespace GlobalTheory.TowVal

theorem bddAll_one_iff_valSet_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (f : Rul Xo c), GlobalTheory.GoodPts.BddAll Xo c la 1 f ↔ ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f := by
  intro E _ _ _ H Dw l Xo c la f
  constructor
  · rintro h _ ⟨⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩, rfl⟩
    have h1 := h T io e ho y hy
    rw [map_one, one_mul] at h1
    exact (GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1 _).1 h1
  · intro h T io e ho y hy
    rw [map_one, one_mul, GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1]
    exact h _ ⟨PtV.mk la ho y hy () trivial, rfl⟩

end GlobalTheory.TowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerContinuousRepresentativePowerBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_continuous_representative_power_bound : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → 1 ≤ (D.sp.Y 0).rank → ∃ m : ℕ, ∀ u : (MP R).Vec, ∃ C : ℝ, ∀ y : X.B.I.GA, ‖GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) y‖ ≤ C * (GlobalTheory.Count.tau1 X.B.I y)⁻¹ ^ m := by
  first | exact @GlobalTheory.ConjRepBound.contRep_bound | exact GlobalTheory.ConjRepBound.contRep_bound | (intros; apply GlobalTheory.ConjRepBound.contRep_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsProperModelOfExtendsFibreIsogenyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_model_of_extends_fibreIsogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  first | exact @GlobalTheory.HkIntegral.isProper_of_ext | exact GlobalTheory.HkIntegral.isProper_of_ext | (intros; apply GlobalTheory.HkIntegral.isProper_of_ext <;> assumption)
end

