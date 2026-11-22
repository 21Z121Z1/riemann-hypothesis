import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0035
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnGramSchmidtUpperTriangularFactor
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection.GSSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Mat

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : Set W}

theorem cdo_det {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) : ContDiffOn ℝ ∞ (fun w => (f w).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

theorem cdo_inv {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hd : ∀ w ∈ s, (f w).det ≠ 0) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine ((cdo_det f hf).inv hd).mul (cdo_det _ fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf _ _

theorem cdo_mul {m : Type} [Fintype m] (f g : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun w => g w i j) s) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w * g w) i j) s := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)

end Mat

theorem contDiff_nmat (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => mat (nmat X w) τ a b := by
  show ContDiff ℝ ∞ fun w : V (nd X) => nmat X w τ a b
  unfold nmat
  split_ifs
  · exact ((EuclideanSpace.proj _ : V (nd X) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  · exact contDiff_const
  · exact contDiff_const

theorem contDiff_Gw (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => PoinPf.Gw X w τ a b := by
  simp only [PoinPf.Gw, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul
    (ContDiff.sum fun l _ => (contDiff_nmat X τ l a).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_nmat X τ k b)

theorem blk_det_on (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (c : Fin r) :
    ∀ w ∈ {w : V (nd X) | cpt X x w ∈ X.dom}, (FrameDegreeData.blk (PoinPf.Gw X w τ) c).det ≠ 0 := by
  intro w hw
  have h := FrameDegreeData.blk_det X hw τ c
  rwa [gram_cpt X hx] at h

theorem cdo_gsU (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (j c : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsU X w τ j c) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  simp only [gsU, FrameDegreeData.uMat, Matrix.of_apply]
  split_ifs with h1 h2
  · exact contDiffOn_const
  · refine ContDiffOn.neg ?_
    simp only [Matrix.vecMul, dotProduct]
    refine ContDiffOn.sum fun m _ => ContDiffOn.mul ?_ ?_
    · exact (contDiff_Gw X τ c (Fin.castLE c.isLt.le m)).contDiffOn
    · exact cdo_inv (fun w => FrameDegreeData.blk (PoinPf.Gw X w τ) c)
        (fun a b => (contDiff_Gw X τ (Fin.castLE c.isLt.le a) (Fin.castLE c.isLt.le b)).contDiffOn)
        (blk_det_on X hx τ c) _ _
  · exact contDiffOn_const

theorem cdo_q (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (i j : Fin r) :
    ContDiffOn ℝ ∞ (fun w => ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) i j)
      {w : V (nd X) | cpt X x w ∈ X.dom} := by
  refine cdo_mul _ _ (fun a b => cdo_mul _ _ (fun a' b' => ?_) (fun a' b' => (contDiff_Gw X τ a' b').contDiffOn) a b)
    (fun a b => ?_) i j
  · exact cdo_gsU X hx τ b' a'
  · exact Complex.conjCLE.contDiff.comp_contDiffOn (cdo_gsU X hx τ a b)

theorem q_eq_dOf (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ) (k : Fin r) :
    ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k = FrameDegreeData.dOf X (cpt X x w) τ k := by
  simp only [FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsU]

theorem cdo_gsS (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (k : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsS X w τ k) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  set S := {w : V (nd X) | cpt X x w ∈ X.dom}
  have hpos : ∀ w ∈ S, 0 < sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re := by
    intro w hw
    rw [q_eq_dOf X hx w τ k]
    exact FrameDegreeData.sgn_dOf_pos X hw τ k
  have hf : ContDiffOn ℝ ∞ (fun w => sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re) S :=
    contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn (cdo_q X hx τ k k))
  refine ContDiffOn.congr (ContDiffOn.inv (hf.sqrt fun w hw => (hpos w hw).ne')
    fun w hw => (Real.sqrt_pos.2 (hpos w hw)).ne') fun w hw => ?_
  have h := hpos w hw
  simp only [gsS]
  congr 2
  rcases FrameDegreeData.sgn_sq X.p0 k with hs | hs <;> rw [hs] at h ⊢
  · rw [one_mul] at h ⊢
    exact abs_of_pos h
  · rw [neg_one_mul] at h ⊢
    exact abs_of_neg (neg_pos.1 h)

theorem gsB_contDiffOn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r},
    IsOrth X x → ∀ (τ : X.Ψ) (a b : Fin r),
      ContDiffOn ℝ ∞ (fun w => gsB X w τ a b) {w | cpt X x w ∈ X.dom} := by
  intro E _ _ _ r X x hx τ a b
  have e : (fun w => gsB X w τ a b) = fun w => gsU X w τ a b * ((gsS X w τ b : ℝ) : ℂ) := by
    funext w
    simp only [gsB, Matrix.mul_diagonal]
  rw [e]
  exact (cdo_gsU X hx τ a b).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (cdo_gsS X hx τ b))

end GlobalTheory.SUChartSection.GSSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitFormalChartEvSubConstantCoeffDvd
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory.FrNil

theorem counit_ev_sub_constantCoeff (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O) :
    (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 1
  set P : MvPolynomial (Fin d) O := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F with hP

  have halg : ((Bialgebra.counitAlgHom O (G.A n)).comp
      ((c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O))) =
      MvPolynomial.aeval (fun _ => (0 : O)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.coe_X,
      MvPowerSeries.map_id]
    rw [(c.isEval n).1 i]
    exact c.aug n i
  have hPc : Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) = constantCoeff F := by
    have := congrArg (fun φ => φ P) halg
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.map_id] at this
    rw [show Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) =
      Bialgebra.counitAlgHom O (G.A n) (c.ev n (P : MvPowerSeries (Fin d) O)) from rfl, this]
    rw [MvPolynomial.aeval_zero', hP, ← coeff_zero_eq_constantCoeff_apply, Algebra.algebraMap_self,
      RingHom.id_apply, MvPolynomial.constantCoeff_eq, coeff_trunc', if_pos]
    intro i
    exact Nat.zero_le _
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α (F - (P : MvPowerSeries (Fin d) O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_trans (Finsupp.le_degree i α) hα.le
  obtain ⟨a, ha⟩ := hN _ hT
  rw [pow_one] at ha
  have hsplit : c.ev n F = c.ev n (F - (P : MvPowerSeries (Fin d) O)) + c.ev n P := by
    rw [← map_add, sub_add_cancel]
  refine ⟨Coalgebra.counit (R := O) a, ?_⟩
  rw [hsplit, map_add, ha, hPc, add_sub_cancel_right]
  rw [show ((p : G.A n)) * a = (p : O) • a by rw [Algebra.smul_def, map_natCast], map_smul, smul_eq_mul]

end GlobalTheory.FrNil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegular
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem isChar_cusp_and_norm_of_reg (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (m k : ℕ) (hm : 0 < m)
    (hk : Reg (Nat.card F) m k) :
    IsChar ℂ ℂ (cusp θ m k) ∧
      ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  obtain ⟨h1, h2⟩ := isChar_psi_rootSum_of_regular F θ hθ m k hm hk
  refine ⟨h1, ?_⟩
  have hip := ipGL_eq_finsum_GL (F := F) (d := m) (psi (rootSum θ k) (Fin m → F))
    (psi (rootSum θ k) (Fin m → F))
  rw [h2] at hip
  have hsq : ((-1 : ℂ) ^ (m - 1)) * star ((-1 : ℂ) ^ (m - 1)) = 1 := by
    rw [star_pow, star_neg, star_one, ← mul_pow]
    norm_num
  have hterm : ∀ x : GL (Fin m) F, cusp θ m k x * star (cusp θ m k x) =
      psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))) := by
    intro x
    simp only [cusp, psiG, star_mul']
    linear_combination (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)))) * hsq
  rw [finsum_congr hterm, ← hip]
  rfl

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters
section
noncomputable section

namespace GlobalTheory.CuspidalIdempotentCharacters

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

theorem isIndCuspChar_iff {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K]
    (s : K →+* ℂ) (χ : G0 Pg r → K) :
    GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.IsIndCuspChar Pg r s χ ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar Pg r s χ := by
  constructor
  · rintro ⟨b, V, i1, i2, i3, σ, hc, hχ⟩
    exact ⟨_, fun PP => ⟨b PP, V PP, i1 PP, i2 PP, i3 PP, σ PP, hc PP, fun _ => rfl⟩, hχ⟩
  · rintro ⟨θ, hθ, hχ⟩
    choose b V i1 i2 i3 σ hc ht using hθ
    exact ⟨b, V, i1, i2, i3, σ, hc, fun g => (hχ g).trans (Finset.prod_congr rfl fun PP _ => ht PP (g PP))⟩

theorem sum_eq_lvlSum {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) (i : Fintype P.H) :
    ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K) = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum P χ := by
  obtain rfl : i = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH P := Subsingleton.elim _ _
  rfl

theorem genericMultOne_iff : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector
  refine forall_congr' fun E => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun Pg =>
    forall_congr' fun r => forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun s => forall_congr' fun ψ => forall_congr' fun _ => forall_congr' fun χ =>
    imp_congr (isIndCuspChar_iff Pg r s χ) ?_
  rw [← sum_eq_lvlSum (P0 Pg r ψ) χ]

section Idem

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem eps_eq_lvlIdem (H : Subgroup G) (ψ : H →* Kˣ) :
    Formalism.MainNotions.PrimeDegreeVariant.eps (⟨H, ψ⟩ : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) = lvlIdem H ψ := by
  classical
  unfold Formalism.MainNotions.PrimeDegreeVariant.eps lvlIdem
  rw [Finset.smul_sum]
  symm
  refine Fintype.sum_of_injective (fun h : H => (h : G)) Subtype.val_injective _ _ ?_ ?_
  · intro x hx
    have : x ∉ H := fun h => hx ⟨⟨x, h⟩, rfl⟩
    simp [this]
  · intro h
    simp [map_inv]

variable {W : Type} [AddCommGroup W] [Module K W]

theorem asAlgebraHom_lvlIdem (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) [Fintype H] :
    τ.asAlgebraHom (lvlIdem H ψ) = (Nat.card H : K)⁻¹ • ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) := by
  unfold lvlIdem
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr (by congr!) fun h _ => ?_
  rw [Representation.asAlgebraHom_single, smul_smul, map_inv]

theorem isIdempotentElem_lvlIdem [CharZero K] (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) :
    IsIdempotentElem (τ.asAlgebraHom (lvlIdem H ψ)) := by
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  rw [IsIdempotentElem, asAlgebraHom_lvlIdem, ← hT, smul_mul_smul_comm, h2, smul_smul, mul_assoc,
    inv_mul_cancel₀ hc, mul_one]

theorem finrank_eq_one_iff [CharZero K] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G)
    (ψ : H →* Kˣ) [Fintype H] :
    Module.finrank K (LinearMap.range (τ.asAlgebraHom (lvlIdem H ψ))) = 1 ↔
      ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) = (Nat.card H : K) := by
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have h := (LinearMap.IsIdempotentElem.isProj_range _ (isIdempotentElem_lvlIdem τ H ψ)).trace
  have e : LinearMap.trace K W (τ.asAlgebraHom (lvlIdem H ψ)) =
      (Nat.card H : K)⁻¹ * ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) := by
    rw [asAlgebraHom_lvlIdem, map_smul, map_sum, smul_eq_mul]
    simp [mul_comm]
  rw [← Nat.cast_eq_one (R := K), ← h, e, inv_mul_eq_one₀ hc, eq_comm]

end Idem

end GlobalTheory.CuspidalIdempotentCharacters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyOnCoverBallsLtTopOfSmoothStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbarEnergyOnCoverBalls_lt_top_of_smooth : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  first | exact @GlobalTheory.n1_lt_infty_of_isSSec | exact GlobalTheory.n1_lt_infty_of_isSSec | (intros; apply GlobalTheory.n1_lt_infty_of_isSSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarGlueSectionByPartitionEqStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_glueSectionByPartition_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  first | exact @GlobalTheory.glue_wdb_eq | exact GlobalTheory.glue_wdb_eq | (intros; apply GlobalTheory.glue_wdb_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrame
section
set_option autoImplicit false

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.CechPer

theorem sum_symm_smul_wedge_eq_zero {B : Type} [CommRing B] [Algebra ℂ B] {g : ℕ}
    (ω : Fin g → Ω[B⁄ℂ]) (S : Fin g → Fin g → B) (hS : ∀ a b, S a b = S b a) :
    ∑ b, ∑ c, S b c • wedge ℂ B (ω b) (ω c) = 0 := by
  set X := ∑ b, ∑ c, S b c • wedge ℂ B (ω b) (ω c) with hX
  have h1 : X = -X := by
    conv_lhs => rw [hX, Finset.sum_comm]
    rw [hX, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [wedge_swap (ω c) (ω b), hS c b, smul_neg]
  have h2 : (2 : B) • X = 0 := by
    rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr h1
  have h3 : algebraMap ℂ B (2⁻¹) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℂ B) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  calc X = (algebraMap ℂ B (2⁻¹) * 2) • X := by rw [h3, one_smul]
    _ = 0 := by rw [mul_smul, h2, smul_zero]

theorem dOne_eq_sum_of_frame {B : Type} [CommRing B] [Algebra ℂ B] {g : ℕ}
    (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ])
    (hc : ∀ a b x, d a (d b x) = d b (d a x))
    (hf : ∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) (ξ : Ω[B⁄ℂ]) :
    dOne ℂ B ξ = ∑ b, ∑ c, d b ((d c).liftKaehlerDifferential ξ) • wedge ℂ B (ω b) (ω c) := by
  induction ξ using ind1 with
  | h0 => simp
  | ha x y hx hy =>
    rw [map_add, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_add, map_add, add_smul]
  | h x y =>
    have hD : ∀ z : B, D ℂ B z = ∑ a, d a z • ω a := fun z ↦ by
      simpa only [Derivation.liftKaehlerDifferential_comp_D] using hf (D ℂ B z)
    have h0 := sum_symm_smul_wedge_eq_zero ω (fun b c ↦ x * d b (d c y))
      (fun a b ↦ by rw [hc a b])
    have h1 : wedge ℂ B (D ℂ B x) (D ℂ B y) =
        ∑ b, ∑ c, (d c y * d b x) • wedge ℂ B (ω b) (ω c) := by
      rw [hD x, hD y, LinearMap.map_sum₂]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [map_smul, LinearMap.map_smul₂, mul_smul]
    rw [dOne_smul_D, h1, ← zero_add (∑ b, ∑ c, (d c y * d b x) • wedge ℂ B (ω b) (ω c)), ← h0,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, Derivation.leibniz,
      smul_eq_mul, smul_eq_mul, add_smul]

theorem dOne_eq_zero_of_frame_of_symm : ∀ (B : Type) [CommRing B] [Algebra ℂ B] (g : ℕ) (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) → (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) → (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) → ∀ k : Fin g → B, (∀ a b, d a (k b) = d b (k a)) → dOne ℂ B (∑ a, k a • ω a) = 0 := by
  intro B _ _ g d ω hc hd hf k hk
  have hl : ∀ c, (d c).liftKaehlerDifferential (∑ a, k a • ω a) = k c := fun c ↦ by
    simp [map_sum, hd]
  rw [dOne_eq_sum_of_frame d ω hc hf]
  simp only [hl]
  exact sum_symm_smul_wedge_eq_zero ω (fun b c ↦ d b (k c)) hk

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseNonvanishingSetOfNeZeroOnComponentsStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_nonvanishingSet_of_ne_zero_on_components : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (T : Set Y), A.IsSec Λ τ → (∀ y, ∃ P ∈ T, P ∈ connectedComponent y) → (∀ P ∈ T, τ (A.pick P) P ≠ 0) → Dense (nz A τ) := by
  first | exact @GlobalTheory.nz_dense_of_ne_zero_on_components | exact GlobalTheory.nz_dense_of_ne_zero_on_components | (intros; apply GlobalTheory.nz_dense_of_ne_zero_on_components <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrix
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem det_secM_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  intro E _ _ _ r X x hx w hw τ
  have hG := FrameDegreeData.ortho_bOf X hw τ
  rw [bOf_cpt X hx w] at hG
  have hm : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [hm, FrameDegreeData.gram_mul, hx τ] at hG
  have hd := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hc : ((yM X w τ).map (starRingEnd ℂ)).det = starRingEnd ℂ (yM X w τ).det :=
    (RingHom.map_det (starRingEnd ℂ) (yM X w τ)).symm
  rw [hc] at hd
  have hJ : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by exact_mod_cast PoinPf.sgn_ne _ _
  have hY : (yM X w τ).det = ((∏ k, gsS X w τ k : ℝ) : ℂ) := by
    rw [yM, Matrix.det_mul, gsB, Matrix.det_mul, Matrix.det_diagonal]
    rw [Matrix.det_of_lowerTriangular _ (fun a b hab => ?_)]
    · rw [gsU, Matrix.det_of_upperTriangular (FrameDegreeData.uMat_upper _)]
      simp only [FrameDegreeData.uMat_diag, Finset.prod_const_one, one_mul]
      have : ∀ i, mat (nmat X w) τ i i = 1 := fun i => by
        simp [mat, nmat]
      simp only [this, Finset.prod_const_one, one_mul]
      push_cast; rfl
    · show nmat X w τ a b = 0
      simp only [nmat]
      have hab' : a < b := hab
      have h1 : ¬ b < a := not_lt.2 (le_of_lt hab')
      rw [dif_neg h1, if_neg (ne_of_lt hab')]
  set t : ℝ := ∏ k, gsS X w τ k with ht
  have hpos : 0 ≤ t := Finset.prod_nonneg fun k _ => inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [hY, Complex.conj_ofReal] at hd
  have htt : ((t * t : ℝ) : ℂ) = 1 := by
    have h2 : (t : ℂ) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det * (t : ℂ) =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [hd, one_mul]
    push_cast
    have h3 : ((t : ℂ) * t) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [← h2]; ring
    exact mul_right_cancel₀ hJ h3
  have htt' : t * t = 1 := by exact_mod_cast htt
  have ht1 : t = 1 := by nlinarith
  rw [secM, Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))) (yM X w τ), hY, ht1, Complex.ofReal_one]

end GlobalTheory.SUChartSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZeroStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → DIn N (subst (up Q u) f) ∧ (In N f → In N (subst (up Q u) f)) := by
  first | exact @GlobalTheory.QLog.dIn_subst_up | exact GlobalTheory.QLog.dIn_subst_up | (intros; apply GlobalTheory.QLog.dIn_subst_up <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogEqSumLinearCoefficientsFormExplicitStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dlog_eq_sum_linearCoefficients_form_explicit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), constantCoeff u = 1 → (∀ n, c.ev n u = charElem χ n) → dlog G χ = ∑ i, lin u i • c.form i := by
  first | exact @GlobalTheory.QLog.Chart.dlog_eq_sum_lin' | exact GlobalTheory.QLog.Chart.dlog_eq_sum_lin' | (intros; apply GlobalTheory.QLog.Chart.dlog_eq_sum_lin' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualBasisCoordMemMaximalIdealOfForallApplyStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualBasis_coord_mem_maximalIdeal_of_forall_apply : ∀ (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M)) (l : Module.Dual O M), (∀ w, l w ∈ IsLocalRing.maximalIdeal O) → ∀ j, lb.repr l j ∈ IsLocalRing.maximalIdeal O := by
  first | exact @GlobalTheory.dualBasis_coord_mem_maximalIdeal | exact GlobalTheory.dualBasis_coord_mem_maximalIdeal | (intros; apply GlobalTheory.dualBasis_coord_mem_maximalIdeal <;> assumption)
end

