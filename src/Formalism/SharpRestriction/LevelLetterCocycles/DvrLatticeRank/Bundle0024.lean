import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0023
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftFrame
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftRingMembership
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0021
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0008

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfI
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLI

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem expS_neg (ζ : LL) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) {i : ℤ} (hi : i < 0) :
    expS W T c ζ a y i = 0 := by
  simp [expS, serC, if_neg (show ¬ (0 ≤ i) by omega)]

theorem ind_fil (τ : K →ₐ[Qp] LL) (U : PowerSeries LL) (hU : PowerSeries.constantCoeff U ≠ 0)
    {g : ℤ → T.V ⊗[Qp] BdR} {m₀ : ℤ} (hg : MLG.Bdd g m₀)
    (hH : ∀ j, serMul U g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j)) :
    ∀ j, g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
  have key : ∀ N : ℕ, ∀ j, j < m₀ + N → g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
    intro N
    induction N with
    | zero => intro j hj; rw [hg j (by omega)]; exact Submodule.zero_mem _
    | succ N ih =>
      intro j hj
      by_cases hjN : j < m₀ + N
      · exact ih j hjN
      · have hj' : j = m₀ + N := by push_cast at hj; omega
        have hs := hH j
        rw [MLG.serMul_eq_sum U hg j ((j - m₀).toNat + 1) le_rfl, Finset.sum_range_succ'] at hs
        have hrest : ∑ k ∈ Finset.range (j - m₀).toNat, PowerSeries.coeff (k + 1) U • g (j - ((k + 1 : ℕ) : ℤ)) ∈
            Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
          refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
          rw [Finset.mem_range] at hk
          exact u3upPf_FilC_anti (PD := PD) T τ (by push_cast; omega) (ih _ (by push_cast; omega))
        have h0 := Submodule.sub_mem _ hs hrest
        rw [add_sub_cancel_left, PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero, sub_zero] at h0
        exact (Submodule.smul_mem_iff _ hU).1 h0
  intro j
  exact key ((j - m₀).toNat + 1) j (by omega)

end Generic

end Formalism.MainNotions.N.Ln34.MLI

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U1linkPf
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

set_option maxHeartbeats 1000000 in
theorem u1link_pf : FirstFrameOfModels := by
  intro D HW F Cm hA hdR hDi hML hMF
  intro l _ hl K LL hG π' E hp9 T₁ T₂ Fm S η m h' up b c α β hIF hHyp
  have hc2 := hHyp.2.1
  have hj2 := hHyp.2.2.2.2.1
  have hηb := hHyp.2.2.2.2.2.1
  have hbS := hHyp.2.2.2.2.2.2.1
  have hh' := hHyp.2.2.2.2.2.2.2.1
  have hm := hHyp.2.2.2.2.2.2.2.2.1
  have hjI : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro τ a ha
    have hd := hj2 τ a ha
    have hb := hbS τ
    have hη := hηb τ
    rw [Set.mem_Icc]
    rcases hd with hd | hd
    · unfold deep at hd
      split_ifs at hd <;> (rw [Set.mem_Icc] at hd; constructor <;> omega)
    · rw [Set.mem_Icc] at hd
      constructor <;> omega
  have hM := u3upPf_MK_pos hl K LL hG h' hh'
  have hMF2 := hMF l hl K LL hG π' E hp9 h' hh' c α β hIF T₂ hc2 hjI
  have hML2 := hML l hl K LL hG π' E hp9 h' hh' T₂ hc2 hjI c
  have hR := UniversalLiftFrames.universal_lift_ring_membership D HW F Cm hA hl K LL hG π' E hp9
  have hT := UniversalLiftFrames.embeddings_card_le_degree D HW K LL hG c
  have hτs := hT.choose_spec.1
  have hcard := hT.choose_spec.2
  have hB := UniversalLiftFrames.universal_lift_basis D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c
  have hrep := hB.choose_spec.choose_spec.choose_spec.choose
  have hbrep := hB.choose_spec.choose_spec.choose_spec.choose_spec
  refine UniversalLiftFrames.universal_lift_frame (W := (HW l).W K 1 LL hG) (PD := (D.loc l).PD K) (GenPf.isDVR (D.loc l) LL)
    (GenPf.isFractionRing LL) Fm (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π'
    (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c S η m up b α β hIF hc2 hjI hMF2 hML2 hM
    hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2.1 hR.2.2.2.2.2.2 hT.choose hτs hcard ?_ ?_ hbS ?_ ?_ ?_ hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep ?_ ?_ ?_ ?_ ?_ ?_ ?_ hHyp
  · exact fun τ ζ hpt => u3upPf_pt_over D HW hG c ζ τ hpt
  · exact fun τ => Nat.lt_of_le_of_lt (Nat.zero_le _) (hηb τ)
  · exact fun τ ζ hpt => ⟨(UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).1,
      (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.1⟩
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.2.1
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.2.2
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_valuation D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt).1
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_valuation D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt).2
  · exact fun τ ζ ζ' hpt hpt' k => UniversalLiftFrames.universal_lift_valuation_points D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ ζ' hpt hpt'
      (hB.choose_spec.choose_spec.choose k) (hrep k)
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).1 hup).1
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).1 hup).2
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).2 hup).1
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).2 hup).2

end Formalism.MainNotions.N.Ln34
end
end

