import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.InternalDirectSumOfParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0032
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitLiftOfLiftParam

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemBiSupOfOrthogonal
section
noncomputable section

namespace GlobalTheory.DownMemRoad

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceMapping GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent GlobalTheory.IndefiniteRowSideFullHecke.InternalDirectSumCriteria

theorem mem_biSup_of_orthogonal {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (S : Set ι) (htop : ⨆ k, U k = ⊤) (horth : ∀ k k', k ≠ k' → U k ⟂ U k')
    {v : V} (hv : ∀ k ∉ S, v ∈ (U k)ᗮ) : v ∈ ⨆ k ∈ S, U k := by
  have hsup : (⨆ k ∈ S, U k) ⊔ (⨆ k ∈ Sᶜ, U k) = ⊤ := by
    rw [← htop]
    exact (iSup_split U (· ∈ S)).symm
  have ho : (⨆ k ∈ S, U k) ⟂ (⨆ k ∈ Sᶜ, U k) := by
    simp only [Submodule.isOrtho_iSup_left, Submodule.isOrtho_iSup_right]
    intro k hk k' hk'
    refine horth _ _ ?_
    rintro rfl
    exact absurd hk' hk
  have hv' : v ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have h1 : (ℂ ∙ v) ⟂ (⨆ k ∈ Sᶜ, U k) := by
      simp only [Submodule.isOrtho_iSup_right]
      intro k hk
      exact (Submodule.span_singleton_le_iff_mem _ _).2 (hv k hk)
    exact h1 (Submodule.mem_span_singleton_self v)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hsup.ge (Submodule.mem_top (x := v)))
  have hb' : b ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have := Submodule.sub_mem _ hv' (ho ha)
    rwa [add_sub_cancel_left] at this
  have hb0 : b = 0 := inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hb' b hb)
  rw [hb0, add_zero]
  exact ha

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem hasParamW_of_thetaOf (hL : ParamLaws N A) {i : N.Loc} (hS : SplitLift N A i)
    (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)} (hx : HasParamX N A i x Sig)
    {σ : what₂.FT} {P : A.AV i} (hθ : thetaOf N A i σ P) (hP : A.ptV i P = some x) :
    HasParamW N A i σ Sig := by
  obtain ⟨P', hP', h1, -, h3, h4, -⟩ := hx
  refine ⟨fun p hp => ?_, ?_, fun w hw => ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · have e : rankIso N A Sig + R.t = R.nV := by
      rw [← h3]
      simp [rankIso, twistIso, muPart, Function.comp_def]
    have e' : R.nV = R.r + R.t := rfl
    omega
  · have e := hloc P' P x hP' hP w hw
    rw [← h4 w hw, ParUpRoad.isoLoc_lift N A hL, hS σ P hθ w hw] at e
    exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)

theorem typeV_isOrtho_eigC {i : N.Loc} (hT : TypeOrth N A i) {x : N.X i} {P : A.AV i}
    (hP : A.ptV i P ≠ some x) : A.typeV i P ⟂ eigC N A i x := by
  unfold eigC
  simp only [Submodule.isOrtho_iSup_right]
  intro P' hP'
  refine hT P P' ?_
  rintro rfl
  exact hP hP'

theorem thetaP_mem (hθ : EachRowHasThetaLift N A) (hL : ParamLaws N A) {i : N.Loc}
    (htop : ⨆ σ, what₂.isot (N.j i) σ = ⊤) (hO : PartOrth N i) (hT : TypeOrth N A i)
    (hS : SplitLift N A i) (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)}
    (hx : HasParamX N A i x Sig) {F : what₂.Mt (N.mu i) (N.j i)} (hF : F ∈ eigC N A i x) :
    what₂.thetaP (N.mu i) (N.j i) F ∈ MjSig N A i Sig := by
  refine mem_biSup_of_orthogonal (what₂.isot (N.j i)) {σ | HasParamW N A i σ Sig} htop hO
    fun σ hσ => ?_
  by_cases h0 : what₂.isot (N.j i) σ = ⊥
  · rw [h0, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  obtain ⟨P, hP⟩ := hθ i σ h0
  have hne : A.ptV i P ≠ some x := fun h => hσ (hasParamW_of_thetaOf N A hL hS hloc hx hP h)
  rw [Submodule.mem_orthogonal]
  intro f hf
  rw [← LinearMap.adjoint_inner_left]
  exact (typeV_isOrtho_eigC N A hT hne).inner_eq (hP.2 ⟨f, hf, rfl⟩) hF

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    EachRowHasThetaLift N A → PartsSum R what₂.Mj what₂.isot → (∀ i, PartOrth N i) →
      (∀ i, TypeOrth N A i) → (∀ i, SplitLift N A i) → ParamLaws N A → (∀ i, LocOfPt N A i) →
      ThetaPMapsEigenspaceInto N A :=
  fun _ _ _ N A hθ hsum hO hT hS hL hloc i _ _ _ hx _ hF =>
    thetaP_mem N A hθ hL (hsum _ (N.j_range i).1 (N.j_range i).2).2 (hO i) (hT i) (hS i) (hloc i) hx hF

theorem downMem : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), ThetaOne N A → Rows.IsotInternal what₂ → PartOrth N i → TypeOrth N A i → ParamLaws N A →
      SplitLift N A i → LocOfPt N A i → DownMem N A i := by
  rintro R H what₂ N A i hθ hI hO hT hL hS hloc x - Sig hx _ ⟨F, hF, rfl⟩
  exact thetaP_mem N A hθ hL (hI _ (N.j_range i).1 (N.j_range i).2).submodule_iSup_eq_top hO hT hS hloc hx hF

end GlobalTheory.DownMemRoad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RiemannFormHermitianLattice
section
open KaehlerDifferential GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem mOm_ιMulti_D_algebraMap (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] (q : ℕ) (w : Fin q → A) :
    ((semiHom_algebraMap k A K).mOm q (exteriorPower.ιMulti A q fun j => D k A (w j)) : DR k K) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (algebraMap A K (w j)) := by
  rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, SemiHom.mDR_ι, SemiHom.m1_D]

theorem mOm_injective_and_omB (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] [Algebra.Smooth k A]
    (B : Subalgebra k K) (hB : ∀ y, y ∈ B ↔ ∃ f : A, algebraMap A K f = y) (q : ℕ) :
    Function.Injective ((semiHom_algebraMap k A K).mOm q) ∧
      ∀ y : DR k K, y ∈ omB k K B q ↔
        ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y := by
  haveI : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)
  haveI : Algebra.FormallyEtale A K := .of_isLocalization (nonZeroDivisors A)
  have hE : IsLocalizedModule (nonZeroDivisors A) (formLin k A K q) :=
    (isLocalizedModule_iff_isBaseChange _ K _).2 (isBaseChange_formLin k A K q)
  haveI : Module.Projective A (⋀[A]^q Ω[A⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A Ω[A⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination A id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat A (⋀[A]^q Ω[A⁄k]) := inferInstance
  haveI : Module.IsTorsionFree A (⋀[A]^q Ω[A⁄k]) := Module.Flat.isTorsionFree
  have hinj : Function.Injective (formLin k A K q) := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors A) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[A]^q Ω[A⁄k])
      (isRegular_of_ne_zero (nonZeroDivisors.coe_ne_zero c))) hc
  have hsm : ∀ (a : A) (z : Om k A q), ((semiHom_algebraMap k A K).mOm q (a • z) : DR k K) =
      algebraMap A K a • ((semiHom_algebraMap k A K).mOm q z : DR k K) := fun a z => by
    rw [SemiHom.mOm_smul]; rfl
  refine ⟨hinj, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · let S : Submodule k (DR k K) :=
      { carrier := {y | ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y}
        add_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a + b, by rw [map_add]; rfl⟩
        zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
        smul_mem' := by
          rintro c _ ⟨a, rfl⟩
          refine ⟨algebraMap k A c • a, ?_⟩
          rw [hsm, ← IsScalarTower.algebraMap_apply, algebraMap_smul] }
    have : omB k K B q ≤ S := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := (hB b).1 hb
      choose w hw using fun j => (hB (v j)).1 (hv j)
      refine ⟨a • exteriorPower.ιMulti A q (fun j => D k A (w j)), ?_⟩
      rw [hsm, mOm_ιMulti_D_algebraMap]
      simp only [hw]
    exact this hy
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span A q Ω[A⁄k] (span_range_derivation k A)
    have hz : z ∈ Submodule.span A
        (⇑(exteriorPower.ιMulti A q) '' {a | Set.range a ⊆ Set.range (D k A)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k A (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [mOm_ιMulti_D_algebraMap]
      exact ιMulti_D_mem_omB_regForms B q fun j => ⟨algebraMap A K (w j), (hB _).2 ⟨w j, rfl⟩⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul a z _ h => rw [hsm]; exact smul_mem_omB_regForms B q ((hB _).2 ⟨a, rfl⟩) h

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeParametersBoundedLatticeEigenfunction
section
noncomputable section

namespace GlobalTheory.SatakeBound

open GlobalTheory.LatHecke

theorem esymm_map_mul (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (fun x => c * x)).esymm k = c ^ k * s.esymm k := by
  rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map,
    ← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  rw [Multiset.mem_powersetCard] at ht
  rw [Function.comp_apply]
  have := Multiset.prod_map_mul (m := t) (f := fun _ => c) (g := fun x => x)
  rw [this, Multiset.map_const', Multiset.prod_replicate, Multiset.map_id', ht.2]

noncomputable def recSeq (s : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => -∑ k ∈ Finset.range (n + 1), s (k + 1) * recSeq s (n - k)
decreasing_by all_goals omega

theorem cast_tri (k : ℕ) : (((k * (k - 1) / 2 : ℕ)) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  rcases k with _ | j
  · simp
  · have h2 : 2 ∣ (j + 1) * j := by rw [mul_comm]; exact (Nat.even_mul_succ_self j).two_dvd
    rw [Nat.add_sub_cancel, Nat.cast_div h2 (by norm_num)]
    push_cast; ring

theorem main : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : Lat O K r → E) (α : Multiset ℂ)
    (C : ℝ), α.card = r → φ ≠ 0 → (∀ L, ‖φ L‖ ≤ C) →
    (∀ k ≤ r, ∀ L, heckeElem k φ L =
      ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • φ L) →
    ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  intro O K _ _ _ _ _ _ _ r E _ _ φ α C hcard hφ hC hT x hx
  have hq1 : (1 : ℝ) < (qRes O : ℝ) := by exact_mod_cast one_lt_qRes (O := O)
  have hq0 : (0 : ℝ) < (qRes O : ℝ) := by linarith
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [Multiset.card_eq_zero] at hcard
    subst hcard
    simp at hx
  obtain ⟨L0, hL0⟩ : ∃ L0, φ L0 ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hφ (funext h)

  set d : ℕ → ℂ := fun k => if k ≤ r then
    (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k else 0 with hd_def
  have hd : ∀ k L, heckeElem k φ L = d k • φ L := by
    intro k L
    by_cases hk : k ≤ r
    · rw [hT k hk L, hd_def]; simp only [hk, if_true]
    · rw [heckeElem_eq_zero (by omega), hd_def]; simp only [hk, if_false, zero_smul]
  have hlin : ∀ (c : ℂ) k L, heckeElem k (fun M => c • φ M) L = (c * d k) • φ L := by
    intro c k L
    rw [heckeElem_eq_sum, ← Finset.smul_sum, ← heckeElem_eq_sum, hd, smul_smul]
  set s : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * d k with hs_def
  set a : ℕ → ℂ := recSeq s with ha_def

  have hA : ∀ n, heckeAll n φ = fun L => a n • φ L := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases n with _ | m
    · funext L
      rw [heckeAll_zero, ha_def, recSeq, one_smul]
    · funext L
      have hid := GlobalTheory.T.heckeOperator_alternating_series_identity O K r E φ (m + 1) L (by omega)
      rw [Finset.sum_range_succ'] at hid
      have key : ∀ k ∈ Finset.range (m + 1),
          ((-1 : ℂ) ^ (k + 1) * (qRes O : ℂ) ^ ((k + 1) * (k + 1 - 1) / 2)) •
            heckeElem (k + 1) (heckeAll (m + 1 - (k + 1)) φ) L = (s (k + 1) * a (m - k)) • φ L := by
        intro k hk
        rw [show m + 1 - (k + 1) = m - k by omega, ih (m - k) (by omega), hlin, smul_smul]
        congr 1
        rw [hs_def]
        ring
      have h0 : ((-1 : ℂ) ^ 0 * (qRes O : ℂ) ^ (0 * (0 - 1) / 2)) = 1 := by simp
      rw [Finset.sum_congr rfl key, h0, one_smul, heckeElem_zero, ← Finset.sum_smul] at hid
      show heckeAll (m + 1) φ L = recSeq s (m + 1) • φ L
      rw [recSeq, neg_smul]
      exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hid)

  set c : ℝ := (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) with hc_def
  have hc0 : 0 < c := Real.rpow_pos_of_pos hq0 _
  set β : Multiset ℂ := α.map (fun y => (c : ℂ) * y) with hβ_def
  have hβs : ∀ k, (-1 : ℂ) ^ k * β.esymm k = s k := by
    intro k
    rw [hβ_def, esymm_map_mul, hs_def, hd_def]
    by_cases hk : k ≤ r
    · simp only [hk, if_true]
      have hreal : c ^ k = (qRes O : ℝ) ^ (k * (k - 1) / 2) *
          (qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) := by
        rw [hc_def, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast (qRes O : ℝ),
          ← Real.rpow_add hq0, cast_tri]
        congr 1
        ring
      have hcomp : (c : ℂ) ^ k = (qRes O : ℂ) ^ (k * (k - 1) / 2) *
          (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow, hreal, Complex.ofReal_mul, Complex.ofReal_pow,
          Complex.ofReal_natCast]
      rw [hcomp]
      ring
    · simp only [hk, if_false, mul_zero]
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard]; omega)]
      simp
  have hrel : ∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [hβs]
    rw [Finset.sum_range_succ']
    have hs0 : s 0 = 1 := by
      rw [hs_def, hd_def]; simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    have ha1 : a (m + 1 - 0) = -∑ k ∈ Finset.range (m + 1), s (k + 1) * a (m - k) := by
      rw [Nat.sub_zero, ha_def, recSeq]
    rw [hs0, ha1]
    have : ∀ k ∈ Finset.range (m + 1), s (k + 1) * a (m + 1 - (k + 1)) = s (k + 1) * a (m - k) := by
      intro k _; rw [show m + 1 - (k + 1) = m - k by omega]
    rw [Finset.sum_congr rfl this]
    ring

  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC L0)
  have hnL0 : 0 < ‖φ L0‖ := norm_pos_iff.mpr hL0
  have hbound : ∀ n, ‖a n‖ ≤ (C / ‖φ L0‖) * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
    intro n
    have h1 : ‖a n‖ * ‖φ L0‖ = ‖heckeAll n φ L0‖ := by
      rw [hA n, norm_smul]
    have h2 : ‖heckeAll n φ L0‖ ≤ (subIdx n L0).ncard * C := by
      rw [heckeAll_eq_sum, Set.ncard_eq_toFinset_card _ (subIdx_finite n L0)]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun M _ => hC M).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 := GlobalTheory.T.ncard_sublatticesOfIndexPrimePower_le O K r n L0
    rw [show C / ‖φ L0‖ * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n =
        C * (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) / ‖φ L0‖ by ring,
      le_div_iff₀ hnL0, h1]
    calc ‖heckeAll n φ L0‖ ≤ (subIdx n L0).ncard * C := h2
      _ ≤ (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) * C :=
          mul_le_mul_of_nonneg_right h3 hC0
      _ = C * (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) := by ring
  have hB : 0 < (qRes O : ℝ) ^ (r - 1) := pow_pos hq0 _
  have hrec := GlobalTheory.T.norm_le_of_recurrence_growth' β a (C / ‖φ L0‖) ((qRes O : ℝ) ^ (r - 1)) r hB
    (by rw [ha_def, recSeq]) hrel hbound
  have hxb := hrec ((c : ℂ) * x) (Multiset.mem_map_of_mem _ hx)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at hxb
  have hcc : (qRes O : ℝ) ^ (r - 1) = c * c := by
    rw [hc_def, ← Real.rpow_add hq0, ← Real.rpow_natCast, Nat.cast_sub hr]
    congr 1
    push_cast
    ring
  rw [hcc] at hxb
  exact le_of_mul_le_mul_left hxb hc0

end GlobalTheory.SatakeBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducibleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_matrixRep_isInternal_irreducible : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)), DirectSum.IsInternal Vs ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  first | exact @GlobalTheory.semisimple_matrix_rep_decomp | exact GlobalTheory.semisimple_matrix_rep_decomp | (intros; apply GlobalTheory.semisimple_matrix_rep_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
section
noncomputable section

namespace GlobalTheory.Proof.SplitPlaceGoodSignature

open NumberField Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem isSplitPl_of_not_isConjPl (w : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E))
    (h : ¬ IsConjPl H w w) : IsSplitPl H w := by
  by_contra hs
  apply h
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  have hc : ∀ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y = c x := fun x y hy =>
    RingOfIntegers.ext hy
  have hle : w.asIdeal ≤ w.asIdeal.comap c := by
    intro x hx
    by_contra hx'
    exact hs ⟨x, hx, fun y hy => by rw [hc x y hy]; exact hx'⟩
  have heq : w.asIdeal = w.asIdeal.comap c :=
    w.isMaximal.eq_of_le (Ideal.comap_ne_top c w.isPrime.ne_top) hle
  intro x y hy
  rw [hc x y hy, ← Ideal.mem_comap, ← heq]

variable (N : NData R H what₂) (A : NAut N)

theorem typePlSplit : TypePlSplit N A := fun k v =>
  isSplitPl_of_not_isConjPl _ (A.plGw_nconj k v v)

theorem isoLoc_lift (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by
  rw [Check.iso_char N A hL, Check.iso_append]
  rfl

theorem goodRow_iff_goodSig {i : N.Loc} {σ : what₂.FT} {Sig : List (Part A.CG)}
    (h : ∀ w, IsSplitPl H w → isoLoc N A Sig w = A.locW i σ w) :
    N.goodRow σ ↔ goodSig N A Sig := by
  have hl : ∀ k, (fun v => A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))) = N.lab k σ := by
    intro k
    funext v
    rw [h _ (typePlSplit N A k v), A.lab_loc i k σ v]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [hl k]

theorem isoLoc_eq_of_hasParamX (hL : ParamLaws N A) {i : N.Loc} (hloc : LocOfPt N A i) {x : N.X i}
    {Sig Sig' : List (Part A.CG)} (h : HasParamX N A i x Sig) (h' : HasParamX N A i x Sig')
    (w : PlE H) (hw : IsSplitPl H w) : isoLoc N A Sig w = isoLoc N A Sig' w := by
  obtain ⟨P, hP, hB⟩ := h
  obtain ⟨P', hP', hB'⟩ := h'
  have e := hloc P P' x hP hP' w hw
  rw [← hB.2.2.2.1 w hw, ← hB'.2.2.2.1 w hw, isoLoc_lift N A hL, isoLoc_lift N A hL] at e
  exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)

theorem goodPart_of_lifts (i : N.Loc) (h1 : ThetaOne N A) (hL : ParamLaws N A)
    (hlift : LiftParam N A i) (hpt : PtLocal N A i) (hloc : LocOfPt N A i) : GoodPart N A i := by
  unfold GoodPart goodPartM
  apply le_antisymm
  · refine iSup₂_le fun σ hσ => ?_
    obtain ⟨hg, Sig₀, hW₀, x₀, hx₀⟩ := hσ
    by_cases hb : what₂.isot (N.j i) σ = ⊥
    · rw [hb]; exact bot_le
    obtain ⟨P, hP⟩ := h1 i σ hb
    obtain ⟨Sig, hW, hB⟩ := hlift σ P hP
    obtain ⟨y, hy⟩ := hpt P x₀ fun w hw => by
      obtain ⟨p, hp, hp'⟩ := hx₀ w hw
      refine ⟨p, ?_, hp'⟩
      rw [hp, ← hB.2.2.2.1 w hw.1, isoLoc_lift N A hL, isoLoc_lift N A hL, hW₀.2.2 w hw.1,
        hW.2.2 w hw.1]
    have hX : HasParamX N A i y Sig := ⟨P, hy, hB⟩
    have hZ : y ∈ ZgoodN N A i := by
      refine ⟨⟨P, hy, _, hB, ?_⟩, Sig, hX, (goodRow_iff_goodSig N A hW.2.2).1 hg⟩
      exact List.mem_map.2 ⟨muPart N A i, by simp, rfl⟩
    refine le_iSup₂_of_le y hZ (le_iSup₂_of_le Sig hX ?_)
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | HasParamW N A i σ Sig}) =>
      what₂.isot (N.j i) σ) σ hW le_rfl
  · refine iSup₂_le fun x hx => iSup₂_le fun Sig hX => ?_
    unfold MjSig
    refine iSup₂_le fun σ hW => ?_
    obtain ⟨-, Sig', hX', hg⟩ := hx
    have hgood : N.goodRow σ := (goodRow_iff_goodSig N A (i := i) fun w hw =>
      (isoLoc_eq_of_hasParamX N A hL hloc hX' hX w hw).trans (hW.2.2 w hw)).2 hg
    have hat : AtM N A i σ := by
      obtain ⟨P, hP, hB⟩ := hX
      refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
      rw [hB.2.2.2.1 w hw.1]
      exact A.pt_loc i P x hP w hw
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | N.goodRow σ ∧ AtM N A i σ}) =>
      what₂.isot (N.j i) σ) σ ⟨hgood, hat⟩ le_rfl

end GlobalTheory.Proof.SplitPlaceGoodSignature
end
end

