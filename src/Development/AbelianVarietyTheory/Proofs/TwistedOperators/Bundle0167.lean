import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoPlaceComponentsFiniteAdelicUnitary
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Filter Topology

namespace GlobalTheory.PlaceLimit

theorem sum_placeIdem {D : D7} {ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F}
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∑ v ∈ A, ε v = pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  choose α h0 h1 h2 using hε
  refine Prod.ext ?_ ?_
  · change fstA D.host.F (∑ v ∈ A, ε v) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun v _ => by rw [h0]; rfl
  · change sndA D.host.F (∑ v ∈ A, ε v) = GlobalTheory.LevelClosure.cutIdem A
    rw [map_sum]
    refine RestrictedProduct.ext _ _ fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (∑ v ∈ A, sndA D.host.F (ε v)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (GlobalTheory.LevelClosure.cutIdem A)
    have e : ∀ v, sndA D.host.F (ε v) = α v := fun v => by rw [h0]; rfl
    rw [map_sum]
    simp only [e]
    by_cases hw : w ∈ A
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw,
        Finset.sum_eq_single w (fun v _ hv => h2 v w (Ne.symm hv)) (fun h => absurd hw h), h1]
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw]
      exact Finset.sum_eq_zero fun v hv => h2 v w fun h => hw (h ▸ hv)

theorem pair_cutIdem_mul_self {F : Type} [Field F] [NumberField F] (A : Finset (HeightOneSpectrum (𝓞 F))) :
    pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) * pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) =
      pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  refine Prod.ext (mul_zero _) ?_
  change GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A = GlobalTheory.LevelClosure.cutIdem A
  refine RestrictedProduct.ext _ _ fun w => ?_
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A) =
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A)
  rw [map_mul]
  by_cases hw : w ∈ A
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw, one_mul]
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw, zero_mul]

theorem tendsto_cut_mul {D : D7} {z : AE D} (hz : infPart D z = 0) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) * z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h : Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) atTop (𝓝 (pairA D.host.F 0 1)) := by
    have := GlobalTheory.LevelClosure.tendsto_cutIdem_mul (1 : Af D.host.F)
    simp only [mul_one] at this
    exact (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds this
  have h2 := h.smul_const z
  have e : pairA D.host.F 0 1 • z = z := by
    rw [Algebra.smul_def, mul_comm]
    exact GlobalTheory.PlaceDatum.mul_pair_one hz
  rw [e] at h2
  simpa only [Algebra.smul_def] using h2

theorem tendsto_mix {D : D7} (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) atTop (𝓝 (Formalism.L2.Theta.mt V g)) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h1 : infPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1 i j) (show infHom V g = 1 from hg)
  have h2 : infPart D (Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = 0 := by
    rw [RingHom.map_sub, h1, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (RingHom.map_one _).symm
    · exact (RingHom.map_zero _).symm
  have h3 := (tendsto_cut_mul h2).add_const ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
  rw [sub_add_cancel] at h3
  refine h3.congr fun A => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem eq_mix_of_mul {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {f : R} (hf : f * f = f)
    {a a' b b' : Matrix n n R} (ha : a * a' = 1) (hb : b' * b = 1)
    (h : b = f • a + (1 - f) • (1 : Matrix n n R)) : b' = f • a' + (1 - f) • (1 : Matrix n n R) := by
  have : b * (f • a' + (1 - f) • (1 : Matrix n n R)) = 1 := by
    rw [h, GlobalTheory.IdemSupport.mix_mul hf, ha, one_mul, GlobalTheory.IdemSupport.mix_self]
  calc b' = b' * (b * (f • a' + (1 - f) • (1 : Matrix n n R))) := by rw [this, mul_one]
    _ = _ := by rw [← mul_assoc, hb, one_mul]

theorem tendsto_components : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V → ∀ (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) → Filter.Tendsto gs Filter.atTop (nhds g) := by
  intro D V g hg ε hε gs hgs
  simp only [sum_placeIdem hε] at hgs
  have hinv : ∀ A, Formalism.L2.Theta.mt V (gs A)⁻¹ =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g⁻¹ +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := fun A =>
    eq_mix_of_mul (by rw [← RingHom.map_mul, pair_cutIdem_mul_self])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, inv_mul_cancel, GlobalTheory.IdemSupport.mt_one]) (hgs A)
  have h1 := (tendsto_mix V hg).congr fun A => (hgs A).symm
  have h2 := (tendsto_mix V (inv_mem hg)).congr fun A => (hinv A).symm
  refine tendsto_subtype_rng.2 (Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_)
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

end GlobalTheory.PlaceLimit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistDatumValueEqProdLocalResidueValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

theorem omegaQ_one_eq_prod_qLoc : ∀ (D : D7) (a b r : ℕ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)),
      omegaQ Q r ξ 1 y = ∏ PP ∈ Q, qLoc r PP (ξ PP) (y PP) := by
  intro D a b r Q ξ y
  unfold omegaQ
  by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dif_pos h, ← Finset.prod_attach Q (fun PP => qLoc r PP (ξ PP) (y PP))]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [zpow_one, qLoc, dif_pos (h PP.1 PP.2)]
  · rw [dif_neg h]
    push_neg at h
    obtain ⟨PP, hPP, hn⟩ := h
    refine (Finset.prod_eq_zero hPP ?_).symm
    rw [qLoc, dif_neg]
    rintro ⟨h1, h2⟩
    exact hn h1 h2

end GlobalTheory.StepVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistPlaceDatumParabolicMove
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParabolicDatum

section Ring

variable {κ : Type} [CommRing κ] {a b r : ℕ}

theorem tri_zero {n : ℕ} {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) (i j : Fin n) (hi : r ≤ i.val) (hj : j.val < r) :
    g.val i j = 0 := by
  rw [Formalism.L2.DIV.mem_blockTri] at hg
  apply hg
  simp only [Formalism.L2.DIV.blk2, if_pos hj, if_neg (not_lt.mpr hi)]
  exact Nat.zero_lt_one

theorem lowZero_mul {c : ℕ} {x : Matrix (Fin c) (Fin b) κ} {y : Matrix (Fin b) (Fin a) κ}
    (hx : LowZero r x) (hy : LowZero r y) : LowZero r (x * y) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < r
  · rw [hx i l hi hl, zero_mul]
  · rw [hy l j (not_lt.mp hl) hj, mul_zero]

theorem lowZero_of_tri {n : ℕ} {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) : LowZero r g.val := fun i j hi hj => tri_zero hg i j hi hj

theorem topL_eq (ha : r ≤ a) (hb : r ≤ b) (y : Matrix (Fin b) (Fin a) κ) :
    topL r y = y.submatrix (Fin.castLE hb) (Fin.castLE ha) := by
  ext i j
  have hij : i.val < b ∧ j.val < a := ⟨lt_of_lt_of_le i.isLt hb, lt_of_lt_of_le j.isLt ha⟩
  simp only [topL, dif_pos hij, Matrix.submatrix_apply]
  rfl

theorem topL_mul {c : ℕ} (ha : r ≤ a) (hb : r ≤ b) (hc : r ≤ c) (x : Matrix (Fin c) (Fin b) κ)
    {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) : topL r (x * y) = topL r x * topL r y := by
  rw [topL_eq ha hc, topL_eq hb hc, topL_eq ha hb]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hb) (Fin.castLE_injective hb) _ _ ?_ fun l => rfl
  intro l hl
  have hrl : r ≤ l.val := by
    by_contra hlt
    exact hl ⟨⟨l.val, not_le.mp hlt⟩, rfl⟩
  rw [hy l _ hrl (by simp), mul_zero]

theorem topL_tri {n : ℕ} (hn : r ≤ n) {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) :
    topL r g.val = (upperLeftBlock hn g).val := by
  rw [topL_eq hn hn, Formalism.L2.DIV.upper_block_val_submatrix hn hg]

theorem det_blockTriangular_eq_mul_diagBlocks {n : ℕ} (hn : r ≤ n) {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hn g) * dBlk (blk2 r) 1 g := by
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Formalism.L2.DIV.upper_block_val_submatrix hn hg, Formalism.L2.DIV.diag_block_det_val 1 hg,
    Matrix.twoBlockTriangular_det (g : Matrix (Fin n) (Fin n) κ) (fun i : Fin n => i.val < r)
      (fun i hi j hj => tri_zero hg i j (not_lt.mp hi) hj)]
  congr 1
  · let e : Fin r ≃ {i : Fin n // i.val < r} :=
      ⟨fun i => ⟨Fin.castLE hn i, i.isLt⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  · let e : {i : Fin n // Formalism.L2.DIV.blk2 r i = 1} ≃ {i : Fin n // ¬ i.val < r} :=
      Equiv.subtypeEquivRight fun i => by
        unfold Formalism.L2.DIV.blk2
        split_ifs with h <;> simp [h]
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl

theorem lowZero_move {G : GL (Fin a) κ} {H : GL (Fin b) κ} (hG : G ∈ blockTri (blk2 r)) (hH : H ∈ blockTri (blk2 r))
    (y : Matrix (Fin b) (Fin a) κ) : LowZero r ((H⁻¹).val * y * G.val) ↔ LowZero r y := by
  constructor
  · intro h
    have hy : y = H.val * ((H⁻¹).val * y * G.val) * (G⁻¹).val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        Units.mul_inv, Matrix.mul_one]
    rw [hy]
    exact lowZero_mul (lowZero_mul (lowZero_of_tri hH) h) (lowZero_of_tri (Subgroup.inv_mem _ hG))
  · intro h
    exact lowZero_mul (lowZero_mul (lowZero_of_tri (Subgroup.inv_mem _ hH)) h) (lowZero_of_tri hG)

theorem det_topL_move (ha : r ≤ a) (hb : r ≤ b) {G : GL (Fin a) κ} {H : GL (Fin b) κ} (hG : G ∈ blockTri (blk2 r))
    (hH : H ∈ blockTri (blk2 r)) {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) :
    (topL r ((H⁻¹).val * y * G.val)).det =
      ((Matrix.GeneralLinearGroup.det G * (dBlk (blk2 r) 1 G)⁻¹ *
        ((Matrix.GeneralLinearGroup.det H)⁻¹ * dBlk (blk2 r) 1 H) : κˣ) : κ) * (topL r y).det := by
  have hHi : H⁻¹ ∈ blockTri (blk2 r) := Subgroup.inv_mem _ hH
  have e1 : topL r ((H⁻¹).val * y * G.val) = (upperLeftBlock hb H⁻¹).val * topL r y * (upperLeftBlock ha G).val := by
    rw [topL_mul ha ha hb _ (lowZero_of_tri hG), topL_mul ha hb hb _ hy, topL_tri hb hHi, topL_tri ha hG]
  have key : (Matrix.GeneralLinearGroup.det G * (dBlk (blk2 r) 1 G)⁻¹ *
      ((Matrix.GeneralLinearGroup.det H)⁻¹ * dBlk (blk2 r) 1 H) : κˣ) =
      Matrix.GeneralLinearGroup.det (upperLeftBlock hb H⁻¹) * Matrix.GeneralLinearGroup.det (upperLeftBlock ha G) := by
    have dG := det_blockTriangular_eq_mul_diagBlocks ha hG
    have dH := det_blockTriangular_eq_mul_diagBlocks hb hHi
    have dinv : dBlk (blk2 r) 1 H⁻¹ = (dBlk (blk2 r) 1 H)⁻¹ :=
      Formalism.L2.DIV.extendOne_inv (Formalism.L2.DIV.blkDet (blk2 r) 1) hH
    rw [map_inv, dinv] at dH
    rw [dG, dH, mul_inv_cancel_right, inv_mul_cancel_right, mul_comm]
  rw [e1, Matrix.det_mul, Matrix.det_mul, key, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply]
  ring

end Ring

theorem omegaQ_parabolic : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (n : ℤ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Q, G PP ∈ blockTri (blk2 r) ∧ H PP ∈ blockTri (blk2 r)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaQ Q r ξ n (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Q, (ξ PP (Matrix.GeneralLinearGroup.det (G PP)) * (ξ PP (dBlk (blk2 r) 1 (G PP)))⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (H PP)))⁻¹ * ξ PP (dBlk (blk2 r) 1 (H PP)))) ^ n : ℂˣ) : ℂ) * omegaQ Q r ξ n y := by
  intro D a b r ha hb Q ξ n G H hGH y
  have hdet : ∀ PP ∈ Q, LowZero r (y PP) →
      (topL r (((H PP)⁻¹).val * y PP * (G PP).val)).det =
        ((Matrix.GeneralLinearGroup.det (G PP) * (dBlk (blk2 r) 1 (G PP))⁻¹ *
          ((Matrix.GeneralLinearGroup.det (H PP))⁻¹ * dBlk (blk2 r) 1 (H PP)) : (kP PP)ˣ) : kP PP) *
          (topL r (y PP)).det :=
    fun PP hP hy => det_topL_move ha hb (hGH PP hP).1 (hGH PP hP).2 hy
  have hcond : (∀ PP ∈ Q, LowZero r (((H PP)⁻¹).val * y PP * (G PP).val) ∧
      IsUnit (topL r (((H PP)⁻¹).val * y PP * (G PP).val)).det) ↔
      ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det := by
    refine forall₂_congr fun PP hP => ?_
    rw [lowZero_move (hGH PP hP).1 (hGH PP hP).2 (y PP)]
    refine and_congr_right fun hy => ?_
    rw [hdet PP hP hy]
    exact Units.isUnit_units_mul _ _
  unfold omegaQ
  split_ifs with h1 h2 h2
  · simp only [← Units.val_zpow_eq_zpow_val, ← Units.coe_prod, ← Units.val_mul]
    congr 1
    rw [← Finset.prod_attach Q, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [← mul_zpow]
    congr 1
    have hu : (h1 PP.1 PP.2).2.unit =
        (Matrix.GeneralLinearGroup.det (G PP.1) * (dBlk (blk2 r) 1 (G PP.1))⁻¹ *
          ((Matrix.GeneralLinearGroup.det (H PP.1))⁻¹ * dBlk (blk2 r) 1 (H PP.1))) * (h2 PP.1 PP.2).2.unit := by
      ext
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
      exact hdet PP.1 PP.2 (h2 PP.1 PP.2).1
    rw [hu]
    simp only [map_mul, map_inv]
  · exact absurd (hcond.mp h1) h2
  · exact absurd (hcond.mpr h2) h1
  · rw [mul_zero]

end GlobalTheory.ParabolicDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlaceDatumBlockTriangularMove
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem collect_factors {ι : Type} (s : Finset ι) (A B p q : ι → ℂˣ) (u v : ℂ)
    (h : (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹)) * u =
      ((∏ i ∈ s, A i : ℂˣ) : ℂ) * ((∏ i ∈ s, B i : ℂˣ) : ℂ)⁻¹ * v) :
    u = ((∏ i ∈ s, (A i * (B i)⁻¹ * (p i * (q i)⁻¹)) : ℂˣ) : ℂ) * v := by

  have hne : (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _))
  have hu : u = (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹))⁻¹ *
      (((∏ i ∈ s, A i : ℂˣ) : ℂ) * ((∏ i ∈ s, B i : ℂˣ) : ℂ)⁻¹ * v) := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hu]
  push_cast [Units.coe_prod]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv, inv_inv]
  ring

theorem omegaG_blockTri_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, G PP ∈ blockTri (blkOf r t) ∧ H PP ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha (G PP) = upperLeftBlock hb (H PP)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP))) * (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))⁻¹ * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹)) : ℂˣ) : ℂ) * omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) y := by
  intro D a b r t k ha hb hak hbk Pg Q χ ξ G H hGH y

  have hlaw := GlobalTheory.T.typePlaces_localDatum_blockTriangular_law D a b r t k ha hb hak hbk Pg Q χ ξ G H y
    (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val)
    (fun PP hP => (hGH PP hP).1) (fun PP hP => (hGH PP hP).2.1) (fun PP hP => (hGH PP hP).2.2)
    (fun _ _ => rfl)
  exact collect_factors Pg
    (fun PP => ∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP)))
    (fun PP => ∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))
    (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)))
    (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP))) _ _ hlaw

end GlobalTheory.StepLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryBorelPreservesMixedModelLatticeLowerBlock
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.MixStab

variable {L : Type} [Field L]

theorem sum_hi {M : Type} [AddCommMonoid M] (N : ℕ) (f : Fin N → M)
    (hf : ∀ i : Fin N, i.1 < N - N / 2 → f i = 0) : ∑ i, f i = ∑ k, f (hi N k) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := hi N) (f := f)]
  · symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hni => hf i ?_
    by_contra hc
    have := i.isLt
    exact hni (Finset.mem_image.2 ⟨⟨i.1 - (N - N / 2), by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [hi]; omega)⟩)
  · intro x _ y _ hxy
    have := congrArg Fin.val hxy
    simp only [hi] at this
    exact Fin.ext (by omega)

theorem embLow_hi {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (k : Fin (n' / 2)) (l : Fin (n / 2)) :
    embLow n' n z (hi n' k) (hi n l) = z k l := by
  rw [embLow, dif_pos ⟨by simp [hi], by simp [hi]⟩]
  congr 1 <;> ext <;> simp [hi]

theorem embLow_eq_zero {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : r.1 < n' - n' / 2 ∨ c.1 < n - n / 2) : embLow n' n z r c = 0 := by
  rw [embLow, dif_neg (by omega)]

theorem mul_embLow_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n) :
    (A * embLow n' n z * B) r c = ∑ l, (∑ k, A r (hi n' k) * z k l) * B (hi n l) c := by
  rw [Matrix.mul_apply, sum_hi n]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, sum_hi n']
    · simp only [embLow_hi]
    · intro i hi'
      rw [embLow_eq_zero z i _ (Or.inl hi'), mul_zero]
  · intro j hj
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro i _
    rw [embLow_eq_zero z i j (Or.inr hj), mul_zero]

theorem lowBlock_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin (n' / 2)) (c : Fin (n / 2)) :
    (lowBlock A * z * lowBlock B) r c = ∑ l, (∑ k, A (hi n' r) (hi n' k) * z k l) * B (hi n l) (hi n c) := by
  simp only [Matrix.mul_apply, lowBlock, Matrix.submatrix_apply]

theorem exists_hi {N : ℕ} (r : Fin N) (hr : N - N / 2 ≤ r.1) : ∃ k, r = hi N k :=
  ⟨⟨r.1 - (N - N / 2), by have := r.isLt; omega⟩, Fin.ext (by simp only [hi]; omega)⟩

theorem mul_embLow_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (hB : ∀ i j : Fin n, j < i → B i j = 0) (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2) :
    (A * embLow n' n z * B) r c = embLow n' n (lowBlock A * z * lowBlock B) r c := by
  by_cases hc : c.1 < n - n / 2
  · rw [embLow_eq_zero _ r c (Or.inr hc), mul_embLow_mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hB (hi n l) c (Fin.lt_def.2 (by simp only [hi]; omega)), mul_zero]
  · have hr : n' - n' / 2 ≤ r.1 := by omega
    obtain ⟨r', rfl⟩ := exists_hi r hr
    obtain ⟨c', rfl⟩ := exists_hi c (by omega)
    rw [mul_embLow_mul_apply, embLow_hi, lowBlock_mul_apply]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_mixLat_iff {n' n : ℕ} (x : Matrix (Fin n') (Fin n) L) : x ∈ mixLat L n' n ↔
    ∀ r c, (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧
      (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) := Iff.rfl

theorem borel_mid_int {σ : L →+* L} {N : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {b : GU σ N}
    (hb : IsBorelU b) (i : Fin N) (hi' : i.rev = i) : b.1.1 i i ∈ intL L := by
  have h := P.fSatake_unit_diag hb i
  rw [hi'] at h
  have h2 := congrArg Valued.v h
  rw [map_mul, hv, map_one] at h2
  rw [mem_intL]
  by_contra hc
  rw [not_le] at hc
  have : (1 : WithZero (Multiplicative ℤ)) < Valued.v (b.1.1 i i) * Valued.v (b.1.1 i i) := one_lt_mul'' hc hc
  rw [h2] at this
  exact lt_irrefl _ this

theorem row_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (hA : ∀ i j : Fin n', j < i → A i j = 0)
    (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) (r : Fin n') (hr : n' / 2 ≤ r.1) (j : Fin n) :
    (A * a) r j = A r r * a r j := by
  rw [mem_mixLat_iff] at ha
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · intro i _ hir
    rcases lt_or_gt_of_ne hir with h1 | h1
    · rw [hA r i h1, zero_mul]
    · rw [(ha i j).1 (Or.inl (by have := Fin.lt_def.1 h1; omega)), mul_zero]
  · simp

theorem borel_mul_mem {σ : L →+* L} {n' n : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ n} {h : GU σ n'}
    (hg : IsBorelU g) (hh : IsBorelU h) (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) :
    (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n := by
  have ha' := (mem_mixLat_iff a).1 ha
  rw [mem_mixLat_iff]
  intro r c
  constructor
  · intro hrc
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [row_mul_eq _ hh a ha r (by omega)]
    rcases hrc with hr | ⟨hr, hc⟩
    · rw [(ha' r j).1 (Or.inl hr), mul_zero, zero_mul]
    · by_cases hjc : j.1 ≤ c.1
      · rw [(ha' r j).1 (Or.inr ⟨hr, by omega⟩), mul_zero, zero_mul]
      · rw [hg j c (Fin.lt_def.2 (by omega)), mul_zero]
  · intro hr hc
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · rw [row_mul_eq _ hh a ha r hr]
      by_cases hz : a r c = 0
      · rw [hz, mul_zero, zero_mul]; exact zero_mem _
      · have h1 : ¬ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2) := fun e => hz ((ha' r c).1 e)
        have hrr : r.rev = r := Fin.ext (by rw [Fin.val_rev]; omega)
        have hcc : c.rev = c := Fin.ext (by rw [Fin.val_rev]; omega)
        exact mul_mem (mul_mem (borel_mid_int hv hh r hrr) ((ha' r c).2 hr hc)) (borel_mid_int hv hg c hcc)
    · intro j _ hjc
      rcases lt_or_gt_of_ne hjc with h1 | h1
      · rw [row_mul_eq _ hh a ha r hr, (ha' r j).1 (Or.inr ⟨hr, by have := Fin.lt_def.1 h1; omega⟩), mul_zero, zero_mul]
      · rw [hg j c h1, mul_zero]
    · simp

end GlobalTheory.SphTheta.MixStab

namespace GlobalTheory.SphTheta

open MixStab in

theorem borel_mixLat_lowBlock : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ a : Matrix (Fin n') (Fin n) L, a ∈ mixLat L n' n → (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ∃ a ∈ mixLat L n' n, (∀ (r : Fin n') (c : Fin n), c.1 < n - n / 2 → a r c = 0) ∧ (h.1.1 * embLow n' n z * g.1.1 : Matrix (Fin n') (Fin n) L) = a + embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1) := by
  intro L _ _ ϖ σ q hU n n' g h hg hh
  refine ⟨fun a ha => borel_mul_mem hU.2.1 hg hh a ha, fun z => ?_⟩
  have key : ∀ (r : Fin n') (c : Fin n), n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2 →
      (h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1)) r c = 0 := fun r c e => by
    rw [Matrix.sub_apply, sub_eq_zero]
    exact mul_embLow_mul_eq _ _ hg _ r c e
  refine ⟨h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1), ?_,
    fun r c hc => key r c (Or.inr hc), (sub_add_cancel _ _).symm⟩
  rw [mem_mixLat_iff]
  intro r c
  refine ⟨fun e => key r c (by omega), fun _ hc => ?_⟩
  rw [key r c (Or.inr hc)]
  exact zero_mem _

end GlobalTheory.SphTheta
end
end

