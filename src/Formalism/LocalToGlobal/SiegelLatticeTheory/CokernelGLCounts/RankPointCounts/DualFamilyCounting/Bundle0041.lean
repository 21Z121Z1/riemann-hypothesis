import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0027
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PerpendicularDefinitionHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUnram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0012
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldMore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0039
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0037
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0040
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjFrameRow

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensJordanL
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section JL

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M) (p : PlF D)

theorem jl_bc_smulO (o : 𝓞 D.host.E) (x : (VS D).V) :
    L.bc p (o • x) = (D.s.atP p).ιE (o : D.host.E) • L.bc p x := by
  rw [← L.bc_smul p]
  congr 1
  first
    | rfl
    | exact (algebraMap_smul D.host.E o x).symm

theorem jl_iE_mem (hA : Agree δ M p) (o : 𝓞 D.host.E) : (D.s.atP p).ιE (o : D.host.E) ∈ (M p).L.O := by
  rw [hA.2.2.2.1]
  exact PI.CntNotIntW.iE_mem_O D p o

theorem jl_latP_span (hA : Agree δ M p) (S : Set (VS D).V) :
    lattice₂ L p (Submodule.span (𝓞 D.host.E) S) = Submodule.span (M p).L.O (L.bc p '' S) := by
  unfold lattice₂
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.span_induction
      (p := fun x _ => L.bc p x ∈ Submodule.span (M p).L.O (L.bc p '' S)) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    · rw [map_zero]
      exact zero_mem _
    · intro y z _ _ hy hz
      rw [map_add]
      exact add_mem hy hz
    · intro o y _ hy
      rw [jl_bc_smulO L p o y]
      exact Submodule.smul_mem _ (⟨_, jl_iE_mem p hA o⟩ : (M p).L.O) hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem jl_closure {s : 𝓞 D.host.E}
    (hs : s ∈ Submonoid.closure {s : 𝓞 D.host.E | ∃ t : 𝓞 D.host.F, t ∉ p.asIdeal ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = s}) :
    ∃ t : 𝓞 D.host.F, t ∉ p.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', rfl⟩ := hy
    exact ⟨t * t', fun h => (p.isPrime.mem_or_mem h).elim ht ht', map_mul _ _ _⟩

theorem jl_latP_le (hA : Agree δ M p) {A B : Submodule (𝓞 D.host.E) (VS D).V}
    (h : locF (F := D.host.F) (K := D.host.E) p.asIdeal A ≤ locF (F := D.host.F) (K := D.host.E) p.asIdeal B) :
    lattice₂ L p A ≤ lattice₂ L p B := by
  unfold lattice₂
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have haA : a ∈ locF (F := D.host.F) (K := D.host.E) p.asIdeal A :=
    ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
  obtain ⟨s, hs, hsb⟩ := h haA
  obtain ⟨t, ht, rfl⟩ := jl_closure p hs
  have hne := Formalism.L2.SG.Pf.LocUnramP.iotaF_ne p t ht
  have hcc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hne, map_one]
  have hE : (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E)) =
      ((t : D.host.F) : D.host.E) := rfl
  have hbc : L.bc p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • a) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) • L.bc p a := by
    rw [jl_bc_smulO, hE, Formalism.L2.SG.Pf.LocUnramP.iotaE_alg]
  have hmem : L.bc p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • a) ∈
      Submodule.span (M p).L.O (L.bc p '' (B : Set (VS D).V)) :=
    Submodule.subset_span ⟨_, hsb, rfl⟩
  have hy : ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] :=
    Formalism.L2.SG.Pf.LocUnramP.iotaF_inv_mem p t ht
  have hc'O : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∈ (M p).L.O := by
    rw [hA.2.2.2.1, (D.s.atP p).O_def]
    have hI : IsIntegral 𝒪[(D.s.atP p).Fp] ((D.s.atP p).ιF (t : D.host.F))⁻¹ :=
      isIntegral_algebraMap (x := (⟨_, hy⟩ : 𝒪[(D.s.atP p).Fp]))
    exact hI.algebraMap
  have e : L.bc p a = (⟨_, hc'O⟩ : (M p).L.O) • L.bc p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • a) := by
    rw [hbc, Subring.smul_def, smul_smul]
    simp only [hcc, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end JL

section BaseDensityIntegrable

variable {D : Formalism.BasicNotions.D7} (p : PlF D)

theorem jl_not_inv_mem (t : 𝓞 D.host.F) (ht : t ∈ p.asIdeal) (ht0 : (D.s.atP p).ιF (t : D.host.F) ≠ 0) :
    ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∉ 𝒪[(D.s.atP p).Fp] := by
  intro hmem
  have hc := (D.s.atP p).val 1 (t : D.host.F)
  rw [map_one, map_one] at hc
  have h1 : (1 : (D.s.atP p).Fp) ≤ᵥ (D.s.atP p).ιF (t : D.host.F) := by
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp)]
    rw [Valuation.mem_integer_iff] at hmem
    calc ValuativeRel.valuation _ 1 = ValuativeRel.valuation _
          ((D.s.atP p).ιF (t : D.host.F) * ((D.s.atP p).ιF (t : D.host.F))⁻¹) := by
          rw [mul_inv_cancel₀ ht0]
      _ = ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F)) *
          ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F))⁻¹ := map_mul _ _ _
      _ ≤ ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F)) * 1 := mul_le_mul' le_rfl hmem
      _ = ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F)) := mul_one _
  have h2 := hc.mp h1
  have h3 := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.F) p t).mpr ht
  exact absurd h2 (not_le.mpr h3)

theorem jl_unit_iff (t : 𝓞 D.host.F) :
    IsUnit (⟨(D.s.atP p).ιF (t : D.host.F), Formalism.L2.SG.Pf.LocUnramP.iotaF_mem p t⟩ : 𝒪[(D.s.atP p).Fp]) ↔
      t ∉ p.asIdeal := by
  constructor
  · intro hu ht
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
    have hy' : (D.s.atP p).ιF (t : D.host.F) * (y : (D.s.atP p).Fp) = 1 := by
      have h := congrArg Subtype.val hy
      simpa using h
    have hne : (D.s.atP p).ιF (t : D.host.F) ≠ 0 := left_ne_zero_of_mul_eq_one hy'
    apply jl_not_inv_mem p t ht hne
    rw [inv_eq_of_mul_eq_one_right hy']
    exact y.2
  · intro ht
    have hne := Formalism.L2.SG.Pf.LocUnramP.iotaF_ne p t ht
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, Formalism.L2.SG.Pf.LocUnramP.iotaF_inv_mem p t ht⟩, ?_⟩
    apply Subtype.ext
    simp [mul_inv_cancel₀ hne]

theorem jl_dvd_iff (ϖ : 𝒪[(D.s.atP p).Fp]) (hϖ : Irreducible ϖ) (t : 𝓞 D.host.F) :
    ϖ ∣ (⟨(D.s.atP p).ιF (t : D.host.F), Formalism.L2.SG.Pf.LocUnramP.iotaF_mem p t⟩ : 𝒪[(D.s.atP p).Fp]) ↔
      t ∈ p.asIdeal := by
  haveI := (D.s.atP p).lf
  rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    jl_unit_iff, not_not]

end BaseDensityIntegrable

theorem jordan_decomposition_holds : DualityBasisChange.JordanL := by
  intro D δ M hA L u u' hT F0 what₂ hR F' hz hP hI p ϖ hϖ
  obtain ⟨hKc, hFc, -⟩ := field_dictionary_holds D
  obtain ⟨hC, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR _ F' hz rfl hP
  obtain ⟨hLat, -⟩ := (mmChar_of local_unimodular_holds) D u u' hT F0 what₂ hR _ F' hz rfl hP
  have hNd : NondegOn (VS D).hT (UPair D F0 F') := by
    intro x hx hxy
    have hxo : x ∈ orthK (VS D).hT (UPair D F0 F') := by
      simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker]
      intro y hy
      rw [← (VS D).herm.eq x y, hxy y hy, map_zero]
    exact (Submodule.disjoint_def.1 hC.disjoint) x hx hxo
  obtain ⟨hJ1, -⟩ := jordan_splitting_exists D.host.E D.host.F (VS D).V hKc hFc (VS D).hT (VS D).herm
  have hne : {c | ∃ b a, IsJordanIn (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal b a ∧
      c = cJof p.asIdeal a}.Nonempty := by
    obtain ⟨b, a, hba⟩ := hJ1 _ _ hNd hLat hI p.asIdeal p.isMaximal
    exact ⟨_, b, a, hba, rfl⟩
  obtain ⟨b, a, hba, hc⟩ := Nat.sInf_mem hne
  have hcJ : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal = cJof p.asIdeal a := hc
  obtain ⟨hbU, hloc, horth, hdiag, ha0⟩ := hba
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hcard : D.R.rS + 1 + (D.R.rS + 1) = finrank D.host.E (UPair D F0 F') := by rw [hUr, hm]; ring
  let e : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) ≃ Fin (finrank D.host.E (UPair D F0 F')) :=
    finSumFinEquiv.trans (finCongr hcard)
  refine ⟨fun i => L.bc p (b (e i)),
    fun i => ⟨(D.s.atP p).ιF ((a (e i) : 𝓞 D.host.F) : D.host.F), Formalism.L2.SG.Pf.LocUnramP.iotaF_mem p (a (e i))⟩,
    ?_, ?_, ?_, ?_⟩
  ·
    have h1 : Submodule.span (M p).L.O (Set.range fun i => L.bc p (b (e i))) =
        lattice₂ L p (Submodule.span (𝓞 D.host.E) (Set.range b)) := by
      rw [jl_latP_span L p (hA p), ← Set.range_comp]
      congr 1
      ext y
      simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨e.symm j, by simp⟩
    rw [h1]
    exact le_antisymm (jl_latP_le L p (hA p) hloc.le) (jl_latP_le L p (hA p) hloc.ge)
  ·
    intro i j hij
    rw [L.bc_form p]
    show (D.s.atP p).ιE ((VS D).hT (b (e i)) (b (e j))) = 0
    rw [horth _ _ (fun h => hij (e.injective h)), map_zero]
  ·
    intro i
    rw [L.bc_form p]
    show (D.s.atP p).ιE ((VS D).hT (b (e i)) (b (e i))) = _
    rw [hdiag, ← Formalism.L2.SG.Pf.LocUnramP.iotaE_alg p]
    rfl
  ·
    rw [hcJ]
    unfold cJof
    refine Finset.card_equiv e (fun i => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [jl_dvd_iff p ϖ hϖ (a (e i))]
    have h0 := ha0 (e i)
    have hm1 := unitaryAbsoluteValueBounds.mem_pow_iff_le_vF (F := D.host.F) p.isMaximal h0 1
    rw [pow_one] at hm1
    rw [hm1]
    constructor <;> intro h <;> omega

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualFormInverse
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions Formalism.L2.SG.Pf.GluedFormOrthogonality
  Formalism.L2.SG.Pf.DualFormInverse

theorem family_dual_holds : FamDual := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have := h𝔭.isPrime
  have hTop := family_top_holds K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  obtain ⟨hbU, -, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hwn1 : ∀ j, h (w j) (w j) = algebraMap F K (c j) := fun j => (hwn j).1
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j => form_U_orth (hbU i) (hwW j)
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => form_orth_U hs (hbU i) (hwW j)
  have hq0 : algebraMap F K (π : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  have hqS : algebraMap F K (π : F) ∈ SP K 𝔭 := by
    have := (isLocUnif (K := K) hK hF h𝔭 hu).mem
    rwa [jι_eq'] at this
  have hA0 : ∀ i, algebraMap F K ((a i : 𝓞 F) : F) ≠ 0 := fun i => by
    rw [← jι_eq']; exact jι_ne_zero (ha0 i)
  have hC0 : ∀ j, algebraMap F K (c j) ≠ 0 := fun j => (map_ne_zero _).2 (hwn j).2
  have hGr : ∀ j, glueFam K 𝔭 b a π w τ (Sum.inr j) = w j := fun j => rfl
  have hGl : ∀ i, vF 𝔭 (a i) ≠ 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) =
      (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) • (b i + w (τ i)) := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_neg hi]
  have hGl0 : ∀ i, vF 𝔭 (a i) = 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) = b i := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_pos hi]
  have key_ii : ∀ i, h (b i + w (τ i)) (b i + w (τ i)) =
      algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i)) := by
    intro i
    simp only [map_add, LinearMap.add_apply, hbw, hwb, hbn, hwn1]
    ring

  have hgg : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ ^ 2 *
          (algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i))) := by
    intro i hi
    rw [hGl i hi, form_smul_smul, star_inv_pow hF, inv_pow (algebraMap F K (π : F)), key_ii]
    ring
  have hgw : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ * algebraMap F K (c (τ i)) := by
    intro i hi
    rw [hGl i hi, hGr, form_smul_left, star_inv_pow hF, inv_pow (algebraMap F K (π : F)), map_add,
      LinearMap.add_apply, hbw, hwn1, zero_add]
  have hwg : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ * algebraMap F K (c (τ i)) := by
    intro i hi
    rw [hGl i hi, hGr, form_smul_right, inv_pow (algebraMap F K (π : F)), map_add, hwb, hwn1, zero_add]
  have hww : ∀ j, h (glueFam K 𝔭 b a π w τ (Sum.inr j)) (glueFam K 𝔭 b a π w τ (Sum.inr j)) =
      algebraMap F K (c j) := fun j => by rw [hGr, hwn1]
  have hdiag0 : ∀ i, vF 𝔭 (a i) = 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        algebraMap F K ((a i : 𝓞 F) : F) := fun i hi => by rw [hGl0 i hi, hbn]

  have hoff0 : ∀ i, vF 𝔭 (a i) = 0 → ∀ s, s ≠ Sum.inl i →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inl i)) = 0 := by
    intro i hi s hs'
    rcases s with i' | j
    · exact glue_inl_inl hs hbU hbo hwW hwo hτ (fun e => hs' (congrArg Sum.inl e))
    · exact hs.eq_iff.1 (glue_inl_w hbU hwW hwo (fun h1 => absurd hi h1))
  have hoff : ∀ i, vF 𝔭 (a i) ≠ 0 → ∀ s, s ≠ Sum.inl i → s ≠ Sum.inr (τ i) →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inl i)) = 0 ∧
        h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) = 0 := by
    intro i hi s h1 h2
    rcases s with i' | j
    · have hii : i' ≠ i := fun e => h1 (congrArg Sum.inl e)
      exact ⟨glue_inl_inl hs hbU hbo hwW hwo hτ hii,
        glue_inl_w hbU hwW hwo (fun h3 e => hii (hτ i' i h3 hi e))⟩
    · have hj : j ≠ τ i := fun e => h2 (congrArg Sum.inr e)
      exact ⟨hs.eq_iff.1 (glue_inl_w hbU hwW hwo (fun _ e => hj e.symm)), hwo j (τ i) hj⟩
  have hoffw : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → ∀ s, s ≠ Sum.inr j →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inr j)) = 0 := by
    intro j hj s hs'
    rcases s with i | j'
    · exact glue_inl_w hbU hwW hwo (fun h3 => hj i h3)
    · exact hwo j' j (fun e => hs' (congrArg Sum.inr e))

  have hpair : ∀ i, vF 𝔭 (a i) ≠ 0 → ∀ X Y : K, X ∈ SP K 𝔭 → Y ∈ SP K 𝔭 →
      ∃ κ : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → K, (∀ t, κ t ∈ SP K 𝔭) ∧
        ∀ s, ∑ t, κ t * h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t) =
          if s = Sum.inl i then X else if s = Sum.inr (τ i) then Y else 0 := by
    intro i hi X Y hX hY
    obtain ⟨r, hr, hre⟩ := (mem_noncompactPart_iff hu _ _).1 (hcong i hi)
    rw [jι_eq', map_add] at hre
    have hre' : algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i)) ^ 2 * r := by
      rw [hre]; ring
    have hc := unit_part_c hK hF h𝔭 hu (ha0 i) hi (hcong i hi)
    obtain ⟨e1, e2⟩ := pair_solve (X := X) (Y := Y) (pow_ne_zero (vF 𝔭 (a i)) hq0) (hA0 i) hc.1 hre'
    obtain ⟨m1, m2⟩ := pair_coeffs_mem (𝔭 := 𝔭) (X := X) (Y := Y) ((SP K 𝔭).pow_mem hqS _)
      (unit_part hK hF h𝔭 hu (ha0 i)) hc.2 hr hX hY
    obtain ⟨κ, hκS, hκ⟩ := exists_two (Sum.inl_ne_inr (a := i) (b := τ i)) m1 m2
      (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
    refine ⟨κ, hκS, fun s => ?_⟩
    rw [hκ s]
    by_cases h1 : s = Sum.inl i
    · subst h1
      rw [if_pos rfl, hgg i hi, hgw i hi]
      linear_combination e1
    · by_cases h2 : s = Sum.inr (τ i)
      · subst h2
        rw [if_neg h1, if_pos rfl, hwg i hi, hww]
        linear_combination e2
      · rw [if_neg h1, if_neg h2, (hoff i hi s h1 h2).1, (hoff i hi s h1 h2).2]
        ring
  refine dualF_le_of_inv hs hnd _ hTop ?_
  intro u
  rcases u with i | j
  · by_cases hi : vF 𝔭 (a i) = 0
    · have hAi : (algebraMap F K ((a i : 𝓞 F) : F))⁻¹ ∈ SP K 𝔭 := by
        have := unit_part hK hF h𝔭 hu (ha0 i)
        rwa [hi, pow_zero, mul_one] at this
      obtain ⟨κ, hκS, hκ⟩ := exists_one (p := Sum.inl i) hAi
        (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i
      · subst h1
        rw [if_pos rfl, hdiag0 i hi, inv_mul_cancel₀ (hA0 i)]
      · rw [if_neg h1, hoff0 i hi s h1, mul_zero]
    · obtain ⟨κ, hκS, hκ⟩ := hpair i hi 1 0 (SP K 𝔭).one_mem (SP K 𝔭).zero_mem
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i <;> simp [h1]
  · by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨κ, hκS, hκ⟩ := hpair i hi 0 1 (SP K 𝔭).zero_mem (SP K 𝔭).one_mem
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i <;> simp [h1]
    · simp only [not_exists, not_and] at hj
      have hCj : (algebraMap F K (c j))⁻¹ ∈ SP K 𝔭 := by
        have := (hunit j hj).2
        rwa [map_inv₀] at this
      obtain ⟨κ, hκS, hκ⟩ := exists_one (p := Sum.inr j) hCj
        (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inr j
      · subst h1
        rw [if_pos rfl, hww, inv_mul_cancel₀ (hC0 j)]
      · rw [if_neg h1, hoffw j hj s h1, mul_zero]

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingVectorsExist
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem gluing_vectors_exist : GlueVecsPre := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  have := h𝔭.isPrime
  have hne : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)
  set W := orthK h U with hW
  set m := finrank K W with hm
  set P : Finset (Fin (finrank K U)) := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  have hPc : P.card < m := hc
  have hPm : ∀ i, (P.filter (· < i)).card < m := fun i =>
    lt_of_le_of_lt (Finset.card_filter_le _ _) hPc
  let τ : Fin (finrank K U) → Fin m := fun i => ⟨(P.filter (· < i)).card, hPm i⟩
  have hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k := by
    intro i k hi hk e
    exact card_filter_lt_inj P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩) (congrArg Fin.val e)
  have hτl : ∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m := by
    intro i hi
    have := card_filter_lt_lt P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    show (P.filter (· < i)).card + 1 < m
    omega
  choose nF hnpos hncong using fun i => exists_totPos_congr (K := K) h𝔭 hne (a i) (2 * vF 𝔭 (a i))
  let t : Fin m → K := fun j =>
    if hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j then algebraMap F K (nF hj.choose) else 1
  have hts : ∀ j, star (t j) = t j := by
    intro j; simp only [t]; split_ifs
    · exact star_fix hF _
    · exact star_one K
  have htp : ∀ j, TotPos (t j) := by
    intro j; simp only [t]; split_ifs
    · exact hnpos _
    · intro φ; rw [map_one]; simp
  have htpart : ∀ i, vF 𝔭 (a i) ≠ 0 → t (τ i) = algebraMap F K (nF i) := by
    intro i hi
    have hj : ∃ i', vF 𝔭 (a i') ≠ 0 ∧ τ i' = τ i := ⟨i, hi, rfl⟩
    simp only [t, dif_pos hj]
    rw [hτ _ _ hj.choose_spec.1 hi hj.choose_spec.2]
  have htnp : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → t j = 1 := by
    intro j hj
    have : ¬ ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j := fun ⟨i, hi, e⟩ => hj i hi e
    simp only [t, dif_neg this]
  let h' : W →ₗ⋆[K] W →ₗ[K] K := (LinearMap.lcomp K K W.subtype).comp (h.comp W.subtype)
  have h'a : ∀ x y : W, h' x y = h x y := fun x y => rfl
  have hsym' : ∀ x y : W, star (h' x y) = h' y x := by
    intro x y; rw [h'a, h'a, ← starRingEnd_apply]; exact hs.eq _ _
  have hpos' : ∀ x : W, x ≠ 0 → TotPos (h' x x) := by
    intro x hx φ; rw [h'a]; exact hpos x x.2 (fun e => hx (Subtype.ext e)) φ
  have hm1 : m - 1 + 1 = m := by omega
  obtain ⟨v, ho, hv1, hvl⟩ := exists_presc_family hK h' hsym' hpos' (m - 1) (by omega)
    (fun j => t (Fin.cast hm1 j)) (fun j => hts _) (fun j => htp _)
  let w : Fin m → V := fun j => (v (Fin.cast hm1.symm j) : V)
  have hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0 := by
    intro j k hjk
    exact ho _ _ (fun e => hjk (Fin.ext (by have := congrArg Fin.val e; simpa using this)))
  have hwn : ∀ j : Fin m, (j : ℕ) + 1 < m → h (w j) (w j) = t j := by
    intro j hj
    have hne' : Fin.cast hm1.symm j ≠ Fin.last (m - 1) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have := hv1 _ hne'
    simpa [w, h'a] using this
  have hwn0 : ∀ j, h (w j) (w j) ≠ 0 := by
    intro j
    by_cases hj : (j : ℕ) + 1 < m
    · rw [hwn j hj]; exact TotPos.ne_zero' (htp j)
    · have hjl := j.isLt
      have hl : Fin.cast hm1.symm j = Fin.last (m - 1) := by
        ext; simp; omega
      have : v (Fin.cast hm1.symm j) ≠ 0 := by rw [hl]; exact hvl
      exact TotPos.ne_zero' (hpos' _ this)
  have hfix : ∀ j, ∃ x : F, h (w j) (w j) = algebraMap F K x := fun j => by
    obtain ⟨x, hx⟩ := (hF _).1 (by rw [← starRingEnd_apply]; exact hs.eq (w j) (w j))
    exact ⟨x, hx.symm⟩
  choose c hcw using hfix
  obtain ⟨π, s₀, hu⟩ := exists_isUnif0 h𝔭
  refine ⟨π, w, c, τ, fun j => (v _).2, hwo,
    fun j => ⟨hcw j, fun h0 => hwn0 j (by rw [hcw j, h0, map_zero])⟩, hτ, ⟨s₀, hu⟩, ?_, hτl, ?_⟩
  · intro i hi
    have e : algebraMap F K (c (τ i)) = algebraMap F K (nF i) := by
      rw [← hcw, hwn _ (hτl i hi), htpart i hi]
    rw [(algebraMap F K).injective e]
    exact hncong i
  · intro j hj hnp
    have e : c j = 1 := by
      apply (algebraMap F K).injective
      rw [← hcw, hwn j hj, htnp j hnp, map_one]
    rw [e, inv_one, map_one]
    exact ⟨(SP K 𝔭).one_mem, (SP K 𝔭).one_mem⟩

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxHolds
section
namespace Formalism.L2.SG.Pf.NcReal.JX

theorem refNBox_holds : RefNBox := refNBox_of FR.frameRow_holds

end Formalism.L2.SG.Pf.NcReal.JX
end

