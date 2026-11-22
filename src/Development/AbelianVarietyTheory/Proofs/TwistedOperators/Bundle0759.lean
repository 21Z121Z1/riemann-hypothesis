import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0583
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0753
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsFourierJacobiToBessel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0635
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0748
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointMovesRowLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl

noncomputable section
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseTiltMove

variable {D : D7}

theorem incA_inj : Function.Injective (incA D) := by
  haveI : Nontrivial (AF D.host.F) :=
    (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective

theorem incA_apply (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem mulVec_latV_of_rat (S : HSp D) (γ : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (L M : Lat S)
    (hLM : ∀ x ∈ L, γ *ᵥ x ∈ M) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : y ∈ latV S L P) :
    γ.map (incA D) *ᵥ y ∈ latV S M P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, hαP, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨α, hα, hαP, 1, rfl, γ *ᵥ x, hLM x hx, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, incA_apply, one_mul, Algebra.TensorProduct.tmul_mul_tmul,
      ← TensorProduct.tmul_sum]
  | zero => simp only [Matrix.mulVec_zero]; exact (latV S M P).zero_mem
  | add u v _ _ hu hv => rw [Matrix.mulVec_add]; exact (latV S M P).add_mem hu hv
  | neg u _ hu => rw [Matrix.mulVec_neg]; exact (latV S M P).neg_mem hu

theorem exists_rat_of_GQ (S : HSp D) (δ : GA D S) (h : δ ∈ GQ S) :
    ∃ γ : GL (Fin S.rank) D.host.E, mt S δ = γ.val.map (incA D) ∧ mt S δ⁻¹ = (γ⁻¹).val.map (incA D) := by
  obtain ⟨γ, -, hγ⟩ := h
  have e : matHom S δ = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ := hγ.symm
  refine ⟨γ, ?_, ?_⟩
  · show (matHom S δ).val = _
    rw [e]; rfl
  · show (matHom S δ⁻¹).val = _
    rw [map_inv, e, ← map_inv]; rfl

theorem moves_of_rat (S : HSp D) (δ : GA D S) (γ γ' : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (h : mt S δ = γ.map (incA D)) (h' : mt S δ⁻¹ = γ'.map (incA D)) (L M : Lat S)
    (hLM : ∀ x ∈ L, γ *ᵥ x ∈ M) (hML : ∀ x ∈ M, γ' *ᵥ x ∈ L) (P : Pl D → Prop) : Moves S δ L M P := by
  intro y _
  refine ⟨fun hy => h ▸ mulVec_latV_of_rat S γ L M hLM P y hy, fun hy => ?_⟩
  have e : mt S δ⁻¹ *ᵥ (mt S δ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.FinPl.PlacesAdeles.mt_mul, inv_mul_cancel, GlobalTheory.FinPl.PlacesAdeles.mt_one,
      Matrix.one_mulVec]
  rw [← e, h']
  exact mulVec_latV_of_rat S γ' M L hML P _ hy

theorem moves_of_isFinOf (S : HSp D) {δ b : GA D S} (hb : IsFinOf δ b) (L M : Lat S)
    (h : Moves S δ L M (fun _ => True)) : Moves S b L M (fun _ => True) := by
  obtain ⟨-, a, ha, hab⟩ := hb
  have hb' : b = a⁻¹ * δ := by rw [← hab, inv_mul_cancel_left]
  intro y hy
  have hy' := GlobalTheory.FinPl.PlacesAdeles.supp_mulVec S _ δ hy
  rw [hb', GlobalTheory.FinPl.PlacesAdeles.mt_mul, ← Matrix.mulVec_mulVec,
    GlobalTheory.FinPl.PlacesAdeles.mulVec_off (GlobalTheory.FinPl.SuppTwoAsm.ginf_le_grpOff S _ (inv_mem ha)) hy']
  exact h y hy

theorem moves_one (S : HSp D) (L : Lat S) (P : Pl D → Prop) : Moves S 1 L L P := by
  intro y _
  rw [GlobalTheory.FinPl.PlacesAdeles.mt_one, Matrix.one_mulVec]

theorem sumLat_mulVec {n k c : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (M₀ : Matrix (Fin n) (Fin k) D.host.E)
    (Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (a : Matrix (Fin n) (Fin c) D.host.E)
    (𝔟 𝔟' : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (t : Fin c → D.host.E) (hM : γ * M₀ = M₀)
    (ha : γ * a = a * diagonal t) (ht : ∀ p, ∀ u ∈ 𝔟 p, t p * u ∈ 𝔟' p) :
    ∀ x ∈ sumLat M₀ Λ a 𝔟, γ *ᵥ x ∈ sumLat M₀ Λ a 𝔟' := by
  rintro _ ⟨y, hy, u, hu, rfl⟩
  refine ⟨y, hy, fun p => t p * u p, fun p => ht p _ (hu p), ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hM, Matrix.mulVec_mulVec, ha, ← Matrix.mulVec_mulVec]
  congr 2
  funext p
  exact Matrix.mulVec_diagonal _ _ _

section Grid

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem lat_grid (j : ℕ) (h1 : 1 ≤ j) (h : j < D.R.m) :
    G.Λ (.grid D.R.m j) = (G.rowDec j h).lat (G.Λ (.top j)) (stairId D.host.AA D.host.AAbar (D.R.m - 1 - j)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact G.sp.rowLat j' h

variable {G}

theorem tilt_cols {j : ℕ} (hj : j < D.R.m) (hodd : Odd j) {δ : GA D (G.V (.grid D.R.m j))} (hδ : IsTilt G j δ)
    (γ : Matrix (Fin (G.V (.grid D.R.m j)).rank) (Fin (G.V (.grid D.R.m j)).rank) D.host.E)
    (hγ : mt _ δ = γ.map (incA D)) :
    γ * frameMat _ _ (G.rowDec j hj).ι = frameMat _ _ (G.rowDec j hj).ι ∧
      γ * (G.rowDec j hj).a = (G.rowDec j hj).a * diagonal (GlobalTheory.RowShape.tiltSc D j) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, D.R.m - 1 - j = 2 * σ := by
    obtain ⟨a, ha⟩ := D.R.m_even; obtain ⟨b, hb⟩ := hodd; exact ⟨(D.R.m - 1 - j) / 2, by omega⟩
  obtain ⟨h0, he, he'⟩ := hδ.2.2 σ hj hσ
  rw [hγ, ← Matrix.map_mul] at h0 he he'
  have h0 := Matrix.map_injective incA_inj h0
  have he := Matrix.map_injective incA_inj he
  have he' := Matrix.map_injective incA_inj he'
  refine ⟨h0, Matrix.ext fun k p => ?_⟩
  rw [Matrix.mul_diagonal]
  by_cases hp : 2 * p.1 < D.R.m - 1 - j
  · have := congrFun (congrFun he k) ⟨p.1, by omega⟩
    simp only [Matrix.mul_diagonal] at this
    have e1 : (γ * (rowJac G j hj σ hσ).e) k ⟨p.1, by omega⟩ = (γ * (G.rowDec j hj).a) k p := rfl
    have e2 : (rowJac G j hj σ hσ).e k ⟨p.1, by omega⟩ = (G.rowDec j hj).a k p := rfl
    rw [← e1, this, e2]
    simp [GlobalTheory.RowShape.tiltSc, hodd, hp]
  · have := congrFun (congrFun he' k) ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩
    simp only [Matrix.mul_diagonal] at this
    have hq : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) (⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ : Fin σ)).rev = p :=
      Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    have e1 : (γ * (rowJac G j hj σ hσ).e') k ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ = (γ * (G.rowDec j hj).a) k p := by
      simp only [Matrix.mul_apply, GlobalTheory.RowUnf.rowJac, GlobalTheory.RowUnf.jacDec, Matrix.submatrix_apply, id_eq, hq]
    have e2 : (rowJac G j hj σ hσ).e' k ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ = (G.rowDec j hj).a k p := by
      simp only [GlobalTheory.RowUnf.rowJac, GlobalTheory.RowUnf.jacDec, Matrix.submatrix_apply, id_eq, hq]
    rw [← e1, this, e2]
    simp [GlobalTheory.RowShape.tiltSc, hodd, hp]

end Grid

section Main

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem tiltSc_ne_zero (j : ℕ) (p : Fin (D.R.m - 1 - j)) : GlobalTheory.RowShape.tiltSc D j p ≠ 0 := by
  unfold GlobalTheory.RowShape.tiltSc
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact star_ne_zero.2 (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact one_ne_zero

theorem moves_idx (t : T) (B : Frames G) (b : Pts G) (hb : IsBase t B b) (j : ℕ) (hj : j ∈ idx D) :
    Moves _ (b j) (G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN G j) fun _ => True := by
  have hj' : 1 ≤ j ∧ j < 1 + (D.R.m - 2) := List.mem_range'_1.1 hj
  have hjm : j < D.R.m := by omega
  obtain ⟨δ, hδ, hfin⟩ := hb.2.1 j hj
  refine moves_of_isFinOf _ hfin _ _ ?_
  have hN : GlobalTheory.RowShape.rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (GlobalTheory.RowShape.rowId D j) := by
    unfold GlobalTheory.RowShape.rowN; rw [dif_pos hjm]
  rw [lat_grid G j hj'.1 hjm, hN]
  by_cases hodd : Odd j
  · obtain ⟨γ, hγ, hγ'⟩ := exists_rat_of_GQ _ δ hδ.1
    obtain ⟨h0, ha⟩ := tilt_cols hjm hodd hδ γ.val hγ
    set t := GlobalTheory.RowShape.tiltSc D j
    have hinv : (γ⁻¹).val * γ.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h0' : (γ⁻¹).val * frameMat _ _ (G.rowDec j hjm).ι = frameMat _ _ (G.rowDec j hjm).ι := by
      conv_lhs => rw [← h0]
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hdd : diagonal t * diagonal (fun p => (t p)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal,
        show (fun p => t p * (t p)⁻¹) = fun _ => (1 : D.host.E) from funext fun p => mul_inv_cancel₀ (tiltSc_ne_zero j p)]
      exact Matrix.diagonal_one
    have ha' : (γ⁻¹).val * (G.rowDec j hjm).a = (G.rowDec j hjm).a * diagonal (fun p => (t p)⁻¹) := by
      calc (γ⁻¹).val * (G.rowDec j hjm).a
          = (γ⁻¹).val * ((G.rowDec j hjm).a * (diagonal t * diagonal (fun p => (t p)⁻¹))) := by
            rw [hdd, Matrix.mul_one]
        _ = (γ⁻¹).val * (γ.val * (G.rowDec j hjm).a) * diagonal (fun p => (t p)⁻¹) := by
            simp only [ha, Matrix.mul_assoc]
        _ = _ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine moves_of_rat _ δ γ.val (γ⁻¹).val hγ hγ' _ _ ?_ ?_ _
    · refine sumLat_mulVec _ _ _ _ _ _ t h0 ha fun p u hu => ?_
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hu
    · refine sumLat_mulVec _ _ _ _ _ _ (fun p => (t p)⁻¹) h0' ha' fun p u hu => ?_
      obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hu
      rw [← mul_assoc, inv_mul_cancel₀ (tiltSc_ne_zero j p), one_mul]
      exact hz
  · have h1 : δ = 1 := hδ.2.1 (Nat.not_odd_iff_even.1 hodd)
    subst h1
    have hI : GlobalTheory.RowShape.rowId D j = stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) := by
      funext p
      simp [GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc, hodd]
    rw [hI]
    exact moves_one _ _ _

theorem moves_rowN (t : T) (B : Frames G) (b : Pts G) (hb : IsBase t B b) (j : ℕ) (h1 : 1 ≤ j) (hm : j ≤ D.R.m) :
    Moves _ (b j) (G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN G j) fun _ => True := by
  by_cases hj : j ∈ idx D
  · exact moves_idx t B b hb j hj
  rw [hb.2.2 j (by omega) hj]
  by_cases hjm : j < D.R.m
  · have hc : D.R.m - 1 - j = 0 := by
      have : ¬ (1 ≤ j ∧ j < 1 + (D.R.m - 2)) := fun h => hj (List.mem_range'_1.2 h)
      omega
    have hN : GlobalTheory.RowShape.rowN G j = G.Λ (.grid D.R.m j) := by
      unfold GlobalTheory.RowShape.rowN
      rw [dif_pos hjm, lat_grid G j h1 hjm]
      congr 1
      funext p
      exact absurd p.2 (by omega)
    rw [hN]
    exact moves_one _ _ _
  · have hN : GlobalTheory.RowShape.rowN G j = G.Λ (.grid D.R.m j) := by
      unfold GlobalTheory.RowShape.rowN; rw [dif_neg hjm]
    rw [hN]
    exact moves_one _ _ _

end Main

theorem base_moves_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → ∀ j, 1 ≤ j → j ≤ D.R.m → GlobalTheory.FinPl.Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN ch.G j) fun _ => True := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t b hb j h1 hm
  exact moves_rowN t ch.S.B b hb j h1 hm

end GlobalTheory.BaseTiltMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumScalarsEqProductEdgeFactorsRowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_scalars_eq_product_edge_factors_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ (c₁ c₂ : ℂ),
    W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) →
    W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m) →
    c₁ * c₂ = ∏ w : locPl G t, ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  first | exact @GlobalTheory.RowVacScalar.scalars_eq_edgeFactors | exact GlobalTheory.RowVacScalar.scalars_eq_edgeFactors | (intros; apply GlobalTheory.RowVacScalar.scalars_eq_edgeFactors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsFourierJacobiToBesselStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_descends_fourierJacobi_to_bessel : ∀ D : D7, VanFB D := by
  first | exact @GlobalTheory.Asc.VanJac.vanFB | exact GlobalTheory.Asc.VanJac.vanFB | (intros; apply GlobalTheory.Asc.VanJac.vanFB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConjLevelMovesVacuumByCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt resG_compl suppAt_resG isDetAt_detAt resG_one resG_mul actO_actO isHalf_actO)

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem omega_conj_vac_low: ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      W.om (.top t j) (1, (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        (∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he Tm hTm
  change W.om (.top t j) (1, conjPt S j k) (S.Z.vac (.top t j)) = _ • Tm fun x => halfInd e (stdLatO S (.top t j))
    (actO _ _ 1⁻¹ (conjPt S j k)⁻¹ x)
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have he2 : e * e = e := ho.idem
  have hc : e * cA D e = 0 := he.2
  obtain ⟨ε, hε, halg⟩ := GlobalTheory.T.exists_baseIdempotent_of_splitIdempotentSum he
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hsplit : (((1 : GA D (G.V (.top j))), conjPt S j k) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) =
      (1, resG _ ε (conjPt S j k)) * (1, resG _ (1 - ε) (conjPt S j k)) := by
    rw [Prod.mk_mul_mk, one_mul, resG_compl _ hε]
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hS := S.N.selfDual (X := .top j) (by show j ≤ D.R.m; omega)
  have hT := S.N.selfDual (X := .top (j + 1)) (by show j + 1 ≤ D.R.m; omega)
  have hlaw := GlobalTheory.SplitLinear.law_orth hW hS hT ho hc hv.2.theta hv.2.lat one_ne_zero hTm
    (GlobalTheory.SplitLinear.suppAt_one e _) (suppAt_resG _ hε (conjPt S j k) halg.symm) (isDetAt_detAt he2 _ 1)
    (isDetAt_detAt he2 _ (resG _ ε (conjPt S j k)))
  have hvac : Tm (halfInd e (stdLatO S (.top t j))) = S.Z.vac (.top t j) := by
    have := hTm.vac; rwa [one_smul] at this
  rw [hsplit, map_mul, Module.End.mul_apply, GlobalTheory.T.truncatedConjugate_fixes_standardVacuum_topPair S hL ht j hj k hk e he ε hε halg]
  conv_lhs => rw [← hvac]
  refine (hlaw (halfInd e (stdLatO S (.top t j))) (isSBHalf_halfInd e _)).trans ?_
  congr 1
  · rw [detAt_one' he2, detAt_resG_eq he2 hc hε halg, GlobalTheory.T.detIdele_conjugatedTopPoint_eq_prod_local S ht j hj k e he]
    unfold GlobalTheory.SplitLinear.fac
    simp only [splitFacO, map_one, inv_one, one_mul]
    rw [GlobalTheory.T.topPairSourceChar_prod_localIdeles G hL j hj]
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have hm : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1
        (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w))) = 1 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac
      rw [GlobalTheory.T.finiteIdeleModulus_prod_localUnitIdeles _ _ (valuation_gdet_kapAt S hj hk), h1, Real.one_rpow, Real.one_rpow, mul_one]
    rw [hm, Complex.ofReal_one, mul_one]
  · congr 1
    funext x
    apply halfInd_congr
    by_cases hx : IsHalf e x
    · have hinv : (conjPt S j k)⁻¹ = resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹ := by
        rw [← resG_inv_eq hε', ← _root_.mul_inv_rev, resG_compl _ hε]
      have key : actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (conjPt S j k)⁻¹ x =
          actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x :=
        calc _ = actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (1 * 1⁻¹)
              (resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹) x := by rw [one_mul, ← hinv]
          _ = actO _ _ 1 (resG _ (1 - ε) (conjPt S j k)⁻¹)
              (actO _ _ 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x) := (actO_actO _ _ _ _ _).symm
          _ = _ := actO_one_resG_compl he2 hc hε halg _ _ ((isHalf_actO _ _ _).2 hx)
      rw [key]
    · constructor <;> rintro ⟨-, h⟩ <;> exact absurd ((isHalf_actO _ _ _).1 h) hx

end GlobalTheory.TopLevelInv

end
end

