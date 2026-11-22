import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0051
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0036
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0031
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0063
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.FlagUnipotentLattices.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem volSt_conj_self {G : Type} [Group G] (H : Subgroup G) {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

theorem volSt_inf_stab_smul {G X : Type} [Group G] [MulAction G X] (H : Subgroup G) {h : G} (hh : h ∈ H)
    (x : X) : H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  rw [Subgroup.smul_inf, volSt_conj_self H hh]
  congr 1
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, MulAction.mem_stabilizer_iff, mul_smul,
    inv_smul_eq_iff]

theorem volSt {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
    (r k : ℕ) (S : Frames L r k) :
    (∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.K0 ≠ 0 ∧ ∀ h ∈ S.St, S.mu (h • Λ) = S.mu Λ) ∧
    ∀ C, S.IsCls C → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 ∧ 1 ≤ S.wC C ∧
      ∀ h ∈ S.St, S.wC (h • C) = S.wC C := by
  obtain ⟨Λ1, hΛ1, hK0, -⟩ := GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S 1 S.N.one_mem 1 S.N'.one_mem
  have hK : S.K0 = S.St ⊓ stabL L Λ1 := hK0.symm
  have hc : ∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ stabL L Λ) ≠ 0 ∧
      (S.St ⊓ stabL L Λ).relIndex S.K0 ≠ 0 := by
    intro Λ hΛ
    rw [hK]
    exact ⟨(GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ1 hΛ hΛ1 S.St).1, (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ hΛ1 hΛ S.St).1⟩
  have hconj : ∀ h ∈ S.St, S.K0.relIndex (MulAut.conj h • S.K0) ≠ 0 ∧
      (MulAut.conj h • S.K0).relIndex S.K0 ≠ 0 := by
    intro h hh
    have e : MulAut.conj h • S.K0 = S.St ⊓ stabL L (h • Λ1) := by
      rw [hK]; exact (volSt_inf_stab_smul S.St hh Λ1).symm
    rw [e]
    exact hc _ ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ1 hΛ1 hΛ1 S.St).2 h).1
  have hle : S.K0 ≤ S.St := by rw [hK]; exact inf_le_left
  have hmod := (GlobalTheory.T.haarInvVolume_conj_modular_character S.St S.K0 hle hconj).2.2.2
  have hone : ∀ h ∈ S.St, invVol S.K0 (MulAut.conj h • S.K0) = 1 := by
    intro h hh
    obtain ⟨Λ, hΛ, hs⟩ := GlobalTheory.T.unipotent_stabilizes_some_lattice L h _ (GlobalTheory.T.pow_eq_zero_of_mem_hermitianFrameUnipotent L r k S h hh.1)
    exact (hmod _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh).2 (volSt_conj_self _ ⟨hh, hs⟩)
  have hinv : ∀ K' : Subgroup S.GLV, S.K0.relIndex K' ≠ 0 → K'.relIndex S.K0 ≠ 0 → ∀ h ∈ S.St,
      invVol S.K0 (MulAut.conj h • K') = invVol S.K0 K' := by
    intro K' h1 h2 h hh
    rw [(hmod K' h1 h2 h hh).1, hone h hh, one_mul]
  refine ⟨fun Λ hΛ => ⟨(hc Λ hΛ).1, (hc Λ hΛ).2, fun h hh => ?_⟩, ?_⟩
  · unfold Frames.mu
    rw [volSt_inf_stab_smul S.St hh Λ]
    exact hinv _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh
  rintro C ⟨n, hn, n', hn', hC⟩
  obtain ⟨Λ, hΛ, e1, e2, e3⟩ := GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S n hn n' hn'
  rw [← hC] at e2 e3
  obtain ⟨⟨K, hKm, hKi, -⟩, -⟩ := GlobalTheory.T.congruence_subgroup_lattice_stabilizer L S.ϖ S.ϖ_irr Λ hΛ 1
  have a1 : S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 :=
    fun h0 => (hc Λ hΛ).1 (Subgroup.relIndex_eq_zero_of_le_right e2 h0)
  have b1 : K.relIndex (S.St ⊓ stabL L Λ) ≠ 0 :=
    fun h0 => hKi (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  have b2 : (K ⊓ (S.St ⊓ stabL L Λ)) ≤ S.St ⊓ MulAction.stabilizer S.GLV C :=
    fun g hg => ⟨hg.2.1, e3 g hg.2 ((hKm g).1 hg.1).2⟩
  have b3 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex (S.St ⊓ stabL L Λ) ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_eq_zero_of_le_left b2 h0
    rw [Subgroup.inf_relIndex_right] at this
    exact b1 this
  have a2 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans b3 (hc Λ hΛ).2
  refine ⟨a1, a2, ?_, fun h hh => ?_⟩
  · obtain ⟨h, hh, hw, -⟩ := GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup L r k S n hn
    have c1 : S.St ⊓ MulAction.stabilizer S.GLV C ≤ MulAut.conj h • S.K0 :=
      e2.trans (e1.le.trans (inf_le_left.trans hw))
    have c2 := (invVol_mul_pos_le_conj S.K0 (MulAut.conj h • S.K0) _ (hconj h hh).1 (hconj h hh).2
      a1 a2).2.2.1 c1
    have c3 := Subgroup.relIndex_ne_zero_trans a2 (hconj h hh).1
    unfold Frames.wC
    rw [c2, hone h hh, one_mul]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 c3
  · unfold Frames.wC
    rw [volSt_inf_stab_smul S.St hh C]
    exact hinv _ a1 a2 h hh

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardGluingHomKernelsLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GluingKernels

theorem encard_le_of_param {R D β : Type} [CommRing R] [AddCommGroup D] [Module R D] [Finite D]
    (m j : ℕ) (Φ : (Fin m → D) → β) (T : Set β)
    (hT : ∀ t ∈ T, ∃ I : Submodule R D, Nat.card I = j ∧ ∃ x : Fin m → D, (∀ i, x i ∈ I) ∧ Φ x = t) :
    T.encard ≤ ((Nat.card (Submodule R D) * j ^ m : ℕ) : ℕ∞) := by
  haveI : Finite (Submodule R D) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule R D))
  let A := Σ I : {I : Submodule R D // Nat.card I = j}, (Fin m → I.1)
  let Ψ : A → β := fun a => Φ fun i => (a.2 i : D)
  have hsub : T ⊆ Ψ '' Set.univ := by
    intro t ht
    obtain ⟨I, hI, x, hx, rfl⟩ := hT t ht
    exact ⟨⟨⟨I, hI⟩, fun i => ⟨x i, hx i⟩⟩, trivial, rfl⟩
  haveI : Fintype {I : Submodule R D // Nat.card I = j} := Fintype.ofFinite _
  have hA : Nat.card A ≤ Nat.card (Submodule R D) * j ^ m := by
    have h1 : Nat.card A = ∑ I : {I : Submodule R D // Nat.card I = j}, j ^ m := by
      rw [Nat.card_sigma]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [Nat.card_fun, I.2, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
    exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _ Subtype.val_injective)
  calc T.encard ≤ (Ψ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set A).encard := Set.encard_image_le _ _
    _ = (Nat.card A : ℕ∞) := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    _ ≤ _ := by exact_mod_cast hA

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)

theorem sat_gens (d : S.Datum) (Λ : Submodule L.O S.V) (hΛ : S.IsTerm d Λ) :
    ∃ b : Fin ((r + 1) + (r + 1)) → S.V, S.sat Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨hSD, hW, -, h1, h2, hli, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ
  haveI : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.1
  have hfg : (S.sat Λ).FG := by
    haveI : IsNoetherian L.O Λ := isNoetherian_of_fg_of_noetherian Λ hSD.1.1
    exact (isNoetherian_submodule.1 this) _ inf_le_left
  have hsp := (GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant L r k S _ hW.2.2.1 _ hW.2.2.2.1).2.2
  set y := Sum.elim (S.fr d Λ) (S.fr' d Λ) with hy
  have hr : Set.range (y ∘ finSumFinEquiv.symm) = Set.range y :=
    finSumFinEquiv.symm.surjective.range_comp y
  obtain ⟨b, -, hb⟩ := GlobalTheory.OrderBasis.order_basis L (y ∘ finSumFinEquiv.symm)
    (hli.comp _ finSumFinEquiv.symm.injective) (S.sat Λ) hfg (by
      rw [hr]
      apply le_antisymm
      · rw [Submodule.span_le]
        intro x hx
        have hx2 : x ∈ S.ME := hx.2
        rw [← hsp] at hx2
        refine (Submodule.span_le.2 ?_) hx2
        rintro _ ⟨i | i, rfl⟩
        · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
        · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
            (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
      · apply Submodule.span_mono
        rintro _ ⟨i | i, rfl⟩
        · have := (h1 (r + 1) le_rfl (S.fr d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_left this.2⟩
        · have := (h2 (r + 1) le_rfl (S.fr' d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_right this.2⟩)
  exact ⟨b, hb⟩

theorem tauRel_sum (d : S.Datum) (Λ : Submodule L.O S.V) (hΛ : S.IsTerm d Λ) {ι : Type}
    (s : Finset ι) (c : ι → L.O) (w y : ι → S.V) (h : ∀ i, S.TauRel d Λ (w i) (y i)) :
    S.TauRel d Λ (∑ i ∈ s, c i • w i) (∑ i ∈ s, c i • y i) := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ hΛ
  induction s using Finset.induction_on with
  | empty => simpa using ((h4 0 (Submodule.zero_mem _)).1 (Submodule.zero_mem _)).2
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact h3 (c a) (c a).2 _ _ _ _ (h a) ih

theorem encard_kernels_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (Mh : Submodule L.O S.V) (j : ℕ), ((((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) '' {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}).encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d C Mh j
  rcases Set.eq_empty_or_nonempty
    {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j} with h0 | ⟨Λ₀, h₀, hC₀, hM₀, -⟩
  · rw [h0]; simp
  obtain ⟨-, -, -, -, -, b, -, hb⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ₀ h₀
  obtain ⟨-, -, -, -, -, ⟨i₀, hi₀, hbe⟩, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₀ h₀
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  let M₀ : Submodule L.O Mh := (S.M d Λ₀).comap Mh.subtype
  have hcard : Nat.card (Mh ⧸ M₀) = S.q ^ i₀ := by
    rw [← hbe, Frames.be, hM₀]
    rfl
  haveI : Finite (Mh ⧸ M₀) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨g, hg⟩ := sat_gens S d Λ₀ h₀
  rw [hM₀] at hg
  have hgm : ∀ i, g i ∈ Mh := fun i => by rw [hg]; exact Submodule.subset_span ⟨i, rfl⟩
  have hgen : Submodule.span L.O (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) = ⊤ := by
    have h1 : Submodule.span L.O (Set.range fun i => (⟨g i, hgm i⟩ : Mh)) = ⊤ := by
      apply Submodule.map_injective_of_injective Mh.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
      exact hg.symm
    have h2 : (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) =
        M₀.mkQ '' Set.range fun i => (⟨g i, hgm i⟩ : Mh) := by
      rw [← Set.range_comp]; rfl
    rw [h2, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]
  have hsub := (GlobalTheory.SubmoduleCount.card_submodule_and_hom_le L (Mh ⧸ M₀) _ _ hgen).1
  have key := encard_le_of_param (R := L.O) (k - 1) j
    (fun x : Fin (k - 1) → Mh ⧸ M₀ =>
      (LinearMap.ker (Fintype.linearCombination L.O x)).map (Fintype.linearCombination L.O b))
    ((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) ''
      {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}) (by
    rintro _ ⟨Λ, ⟨hΛ, hC, hM, hj⟩, rfl⟩
    obtain ⟨t1, t2, -, t4, t5, -⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ hΛ
    rw [hM] at t1 t5
    have hMM : S.M d Λ = S.M d Λ₀ := by
      have hmem : (S.fr d Λ, S.fr' d Λ) ∈ S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) := by
        have := (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1
        have h2 : S.frameCls (S.fr d Λ) (S.fr' d Λ) = S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) :=
          hC.trans hC₀.symm
        rwa [h2] at this
      exact ((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 _ hmem).2
    have hbL : ∀ i, b i ∈ S.complementLatticeOfDatum d := fun i => by
      rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩
    choose y hy hty using fun i => t1 (b i) (hbL i)
    refine ⟨((S.Ihat d Λ).comap Mh.subtype).map M₀.mkQ, ?_, fun i => M₀.mkQ ⟨y i, hy i⟩, ?_, ?_⟩
    · rw [← hj, Frames.cardI, hMM,
        ← AddSubgroup.relIndex_addSubgroupOf (L := Mh.toAddSubgroup) t5]
      have hk : (S.M d Λ₀).toAddSubgroup.addSubgroupOf Mh.toAddSubgroup =
          M₀.mkQ.toAddMonoidHom.ker := by
        ext x
        exact (Submodule.Quotient.mk_eq_zero M₀).symm
      rw [hk, AddSubgroup.relIndex_ker]
      rfl
    · intro i
      exact ⟨⟨y i, hy i⟩, Submodule.mem_sup_right (Submodule.subset_span ⟨b i, hbL i, hty i⟩), rfl⟩
    · have hz : ∀ c : Fin (k - 1) → L.O,
          Fintype.linearCombination L.O (fun i => M₀.mkQ ⟨y i, hy i⟩) c = 0 ↔
            S.TauRel d Λ (∑ i, c i • b i) 0 := by
        intro c
        rw [t2 _ _ 0 (tauRel_sum S d Λ hΛ Finset.univ c b y hty), sub_zero, hMM,
          Fintype.linearCombination_apply]
        simp only [← map_smul, ← map_sum]
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        simp [M₀]
      ext w
      simp only [Submodule.mem_map, LinearMap.mem_ker, hz, Submodule.mem_inf,
        Submodule.restrictScalars_mem]
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hL : ∑ i, c i • b i ∈ S.complementLatticeOfDatum d := by
          rw [hb]
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        rw [Fintype.linearCombination_apply]
        exact ⟨(t4 _ hL.1).2 ⟨hL, hc⟩, hL.1⟩
      · rintro ⟨hw, hw0⟩
        obtain ⟨hL, ht⟩ := (t4 w hw0).1 hw
        rw [hb] at hL
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hL
        exact ⟨c, ht, Fintype.linearCombination_apply _ _ _⟩)
  have hN : Nat.card (Submodule L.O (Mh ⧸ M₀)) * j ^ (k - 1) ≤
      S.q ^ (S.a.toNat * (2 * r + 2)) * j ^ (k - 1) := by
    refine Nat.mul_le_mul_right _ (hsub.trans ?_)
    rw [hcard, ← pow_mul]
    refine Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul (by omega) (by omega))
  have h3 := key.trans (Nat.cast_le.2 hN)
  have h4 := ENat.toENNReal_le.2 h3
  simpa using h4

end GlobalTheory.HL.GluingKernels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardShortVectorsLe
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem trace_cast_eq_sum_re {K : Type} [Field K] [NumberField K] (z : K) :
    ((Algebra.trace ℚ K z : ℚ) : ℝ) = ∑ τ : K →ₐ[ℚ] ℂ, (τ z).re := by
  have key := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := z)
  have hre := congrArg Complex.re key
  rw [Complex.re_sum] at hre
  rw [← hre]
  simp

theorem card_algHom_eq_two_mul_fDeg {K : Type} [Field K] [NumberField K] (hK : IsTotallyComplex K) :
    Module.finrank ℚ K = 2 * fDeg K := by
  have := hK
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

theorem finrank_le_trace_of_integral {K : Type} [Field K] [NumberField K] (z : 𝓞 K)
    (hre : ∀ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).im = 0) (hpos : ∀ τ : K →ₐ[ℚ] ℂ, 0 < (τ (z : K)).re) :
    (Module.finrank ℚ K : ℝ) ≤ ∑ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := by
  classical
  have hprod : ((∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re : ℝ) : ℂ) = ∏ τ : K →ₐ[ℚ] ℂ, τ (z : K) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact Complex.ext (by simp) (by simp [hre τ])
  have hnorm := Algebra.norm_eq_prod_embeddings (K := ℚ) (E := ℂ) (z : K)
  have h2 : ((((Algebra.norm ℤ z : ℤ) : ℚ) : ℝ) : ℂ) = ((∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re : ℝ) : ℂ) := by
    rw [hprod, ← hnorm, Algebra.coe_norm_int]
    simp
  have hN : (((Algebra.norm ℤ z : ℤ) : ℚ) : ℝ) = ∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re :=
    Complex.ofReal_injective h2
  have hP : (0 : ℝ) < ∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := Finset.prod_pos fun τ _ => hpos τ
  have hN1 : (1 : ℝ) ≤ ∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := by
    rw [← hN] at hP ⊢
    have h3 : (0 : ℤ) < Algebra.norm ℤ z := by exact_mod_cast hP
    have h4 : (1 : ℤ) ≤ Algebra.norm ℤ z := h3
    exact_mod_cast h4
  have hL := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.traceLower (K →ₐ[ℚ] ℂ) (fun τ => (τ (z : K)).re)
    (fun τ => (hpos τ).le) hN1
  simpa only [AlgHom.card] using hL

theorem finrank_le_of_span_range {K V E : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup E] [Module ℝ E] (ι : V →+ E)
    (hs : Submodule.span ℝ (Set.range ι) = ⊤) :
    Module.finrank ℝ E ≤ Module.finrank ℚ K * Module.finrank K V := by
  classical
  let bV := Module.finBasis K V
  let bK := Module.finBasis ℚ K
  let g : Fin (Module.finrank ℚ K) × Fin (Module.finrank K V) → E := fun p => ι (bK p.1 • bV p.2)
  have hsub : Set.range ι ⊆ Submodule.span ℝ (Set.range g) := by
    rintro _ ⟨v, rfl⟩
    rw [← bV.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← bK.sum_repr (bV.repr v j), Finset.sum_smul, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Rat.smul_def, mul_smul, map_ratCast_smul ι K ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hEq : Submodule.span ℝ (Set.range g) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hs]
    exact Submodule.span_le.mpr hsub
  have hc := finrank_range_le_card (R := ℝ) g
  rw [Set.finrank, hEq, finrank_top] at hc
  simpa [Fintype.card_prod] using hc

theorem encard_shortVectors_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → ∀ B : ℝ, 0 ≤ B → (({x : V | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt B) ^ (2 * Module.finrank K V * fDeg K)) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hPD L hL B hB
  classical
  have hK' := hK
  unfold Formalism.HermitianLatticesTheory.IsCMUnram at hK'
  obtain ⟨hTC, hCM, -⟩ := hK'
  have hPD' := hPD
  unfold PD at hPD'
  have hL' := hL
  unfold IsIntLat at hL'
  have hInt := hL'.2
  unfold Formalism.HermitianLatticesTheory.IsIntegralLat at hInt

  have hreal : ∀ (x : V) (τ : K →+* ℂ), (τ (h x x)).im = 0 := by
    intro x τ
    have e1 := hCM τ (h x x)
    have e2 : star (h x x) = h x x := by
      have := hs.eq x x
      simpa [starRingEnd_apply] using this
    rw [e2] at e1
    exact Complex.conj_eq_iff_im.mp e1.symm
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K := by simp
  have hne : Nonempty (K →ₐ[ℚ] ℂ) :=
    Fintype.card_pos_iff.mp (hcard ▸ Module.finrank_pos)

  have htr_pos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
    intro x hx
    have e := trace_cast_eq_sum_re (h x x)
    have hs' : (0 : ℝ) < ∑ τ : K →ₐ[ℚ] ℂ, (τ (h x x)).re :=
      Finset.sum_pos (fun τ _ => hPD' τ.toRingHom x hx) Finset.univ_nonempty
    rw [← e] at hs'
    exact_mod_cast hs'
  obtain ⟨N, ι, hinner, -, -⟩ := Formalism.HermitianLatticesTheory.final_traceReal K V h hs htr_pos
  have hnorm : ∀ x : V, ‖ι x‖ ^ 2 = ∑ τ : K →ₐ[ℚ] ℂ, (τ (h x x)).re := by
    intro x
    rw [← real_inner_self_eq_norm_sq, hinner, trace_cast_eq_sum_re]

  have hlong : ∀ x ∈ L, x ≠ 0 → (Module.finrank ℚ K : ℝ) ≤ ‖ι x‖ ^ 2 := by
    intro x hx hx0
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hInt x hx x hx)
    have hr' : ((r : 𝓞 K) : K) = h x x := hr
    rw [hnorm, ← hr']
    refine finrank_le_trace_of_integral r (fun τ => ?_) (fun τ => ?_)
    · rw [hr']; exact hreal x τ.toRingHom
    · rw [hr']; exact hPD' τ.toRingHom x hx0

  have hshort : ∀ x : V, (∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B) →
      ‖ι x‖ ^ 2 ≤ (Module.finrank ℚ K : ℝ) * B := by
    intro x hx
    rw [hnorm]
    calc ∑ τ : K →ₐ[ℚ] ℂ, (τ (h x x)).re ≤ ∑ _τ : K →ₐ[ℚ] ℂ, B :=
          Finset.sum_le_sum fun τ _ => hx τ.toRingHom
      _ = (Module.finrank ℚ K : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]

  have hinj : Function.Injective ι := by
    intro a b hab
    by_contra hne'
    have hd : a - b ≠ 0 := sub_ne_zero.mpr hne'
    have h0 : ι (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hp := htr_pos (a - b) hd
    have hq : ‖ι (a - b)‖ ^ 2 = ((Algebra.trace ℚ K (h (a - b) (a - b)) : ℚ) : ℝ) := by
      rw [← real_inner_self_eq_norm_sq, hinner]
    rw [h0, norm_zero] at hq
    have : ((Algebra.trace ℚ K (h (a - b) (a - b)) : ℚ) : ℝ) = 0 := by rw [← hq]; ring
    have : Algebra.trace ℚ K (h (a - b) (a - b)) = 0 := by exact_mod_cast this
    exact absurd this hp.ne'

  set E := EuclideanSpace ℝ (Fin N)
  set Es : Submodule ℝ E := Submodule.span ℝ (Set.range ι) with hEs
  let ι' : V →+ Es := AddMonoidHom.mk' (fun x => ⟨ι x, Submodule.subset_span ⟨x, rfl⟩⟩)
    (fun a b => Subtype.ext (map_add ι a b))
  have hι' : ∀ x, ((ι' x : Es) : E) = ι x := fun x => rfl
  have hspan : Submodule.span ℝ (Set.range ι') = ⊤ := by
    have e : Set.range ι' = ((↑) : Es → E) ⁻¹' (Set.range ι) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
    rw [e]
    exact Submodule.span_span_coe_preimage
  have hdim : Module.finrank ℝ Es ≤ 2 * Module.finrank K V * fDeg K := by
    have h1 := finrank_le_of_span_range (K := K) (V := V) ι' hspan
    rw [card_algHom_eq_two_mul_fDeg hTC] at h1
    calc Module.finrank ℝ Es ≤ 2 * fDeg K * Module.finrank K V := h1
      _ = 2 * Module.finrank K V * fDeg K := by ring

  set D : ℝ := (Module.finrank ℚ K : ℝ) with hD
  have hD0 : 0 < D := by
    rw [hD]; exact_mod_cast Module.finrank_pos
  set Λ : AddSubgroup Es := L.toAddSubgroup.map ι'
  have hl0 : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hmin : ∀ y ∈ Λ, y ≠ 0 → Real.sqrt D ≤ ‖y‖ := by
    intro y hy hy0
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hy0 (map_zero ι')
    have e : ‖ι' x‖ = ‖ι x‖ := rfl
    rw [e]
    calc Real.sqrt D ≤ Real.sqrt (‖ι x‖ ^ 2) := Real.sqrt_le_sqrt (hlong x hx hx0)
      _ = ‖ι x‖ := Real.sqrt_sq (norm_nonneg _)
  obtain ⟨hfin, hcount⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.packing Es Λ (Real.sqrt D) (Real.sqrt (D * B))
    hl0 (Real.sqrt_nonneg _) hmin
  have hratio : 2 * Real.sqrt (D * B) / Real.sqrt D = 2 * Real.sqrt B := by
    rw [Real.sqrt_mul hD0.le, mul_div_assoc, mul_div_cancel_left₀ _ hl0.ne']
  rw [hratio] at hcount
  have hbase : (1 : ℝ) ≤ 1 + 2 * Real.sqrt B := by
    have := Real.sqrt_nonneg B
    linarith
  have hpow := pow_le_pow_right₀ hbase hdim

  have hmaps : Set.MapsTo ι' {x | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}
      {y : Es | y ∈ Λ ∧ ‖y‖ ≤ Real.sqrt (D * B)} := by
    rintro x ⟨hx, hxB⟩
    refine ⟨AddSubgroup.mem_map_of_mem ι' hx, ?_⟩
    have e : ‖ι' x‖ = ‖ι x‖ := rfl
    rw [e]
    have := Real.abs_le_sqrt (hshort x hxB)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hinj' : Set.InjOn ι' {x | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B} := by
    intro a _ b _ hab
    apply hinj
    rw [← hι' a, ← hι' b, hab]
  have hle := Set.encard_le_encard_of_injOn hmaps hinj'
  rw [← hfin.cast_ncard_eq] at hle
  calc ((({x | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}.encard : ℕ∞) : ℝ≥0∞))
      ≤ (((({y : Es | y ∈ Λ ∧ ‖y‖ ≤ Real.sqrt (D * B)}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := by
        exact_mod_cast hle
    _ = ENNReal.ofReal (({y : Es | y ∈ Λ ∧ ‖y‖ ≤ Real.sqrt (D * B)}.ncard : ℝ)) := by
        simp
    _ ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt B) ^ (2 * Module.finrank K V * fDeg K)) :=
        ENNReal.ofReal_le_ofReal (hcount.trans hpow)

end GlobalTheory.Mass
end

