import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0020
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0016
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0003

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.GramFlagFamilyOfPositive
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_generic_gram_value (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) {C' Cl Cg cb Cu cT CT C0 A : ℝ}
    (hH : Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (he : F0.e = D.sp.hypE) (hz0 : F0.z = D.zmOf u)
    (Λ : LatV D) (hΛr : IsRowLat D F0 Λ) (F' : FlagU D u') (hT' : IsTermF D Λ (lf D F0) F')
    (hgen : IsGeneric Λ (gS D) (lf D F0) F') : 1 ≤ G0 Λ (gS D) (lf D F0) F' := by
  have hSt : Cnt.Stand D u u' := hH.2.1
  have hPr := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hF : FixedHyp D Λ (lf D F0) := hΛr.2.1
  have hg : gS D ≠ 0 := by
    unfold gS
    exact Nat.mul_ne_zero hSt.2.2.2.2.2.2.2.1.ne_zero hSt.2.2.2.2.2.2.2.2.1.ne_zero
  have hU1 : HU Λ (lf D F0) F' := a_HU Λ hF.1 _ _ hF.2.2.1.2 hT'.1.1.2
  obtain ⟨_, _, h2, h3, _⟩ := lemma_one_section D u (Tu D u') Λ (lf D F0) F' hF hPr hT'.1
  have hbot := generic_B_eq_bot hg hF.2.2.1 hT'.1.1 hF.2.2.2 hT'.2.1 hgen
  have hle := generic_index_one D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz0 Λ hΛr F' hT' hgen
  have hLa : La Λ (gS D) (lf D F0) F' = Thp Λ (lf D F0) F' := le_antisymm hle (c_Thp_le_La hU1)
  have hc1 : Nat.card (gB Λ (gS D) (lf D F0) F') = 1 := by rw [hbot]; exact Nat.card_unique
  have hi : iIdx Λ (gS D) (lf D F0) F' = 1 := by
    unfold iIdx idx
    rw [Submodule.comap_subtype_eq_top.2 hle]
    exact Nat.card_unique
  have hNE : 0 < NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) := by
    unfold NE
    have : (0 : ℝ) < (gS D : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hg
    positivity
  have hlow : NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) ≤ (Nat.card (BQ Λ (lf D F0) F') : ℝ) := by
    rw [hc1, Nat.cast_one, le_div_iff₀ hNE, one_mul] at h2
    exact h2
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ := hΛr.2.1.2.1
  have hdet : 1 ≤ latDet (hS D) (La Λ (gS D) (lf D F0) F') := by
    rw [hLa]
    exact rows_one_le_latDet _ fun x hx y hy =>
      Submodule.mem_one.1 (i_int Λ hun (Submodule.mem_inf.1 hy).1 (Submodule.mem_inf.1 hx).1)
  have hB : 0 < (Nat.card (BQ Λ (lf D F0) F') : ℝ) := lt_of_lt_of_le hNE hlow
  rw [hi, Nat.cast_one, mul_one] at h3
  have hNG : NG Λ (lf D F0) F' = latDet (hS D) (La Λ (gS D) (lf D F0) F') * (Nat.card (BQ Λ (lf D F0) F') : ℝ) := by
    rw [h3]
    field_simp
  unfold G0
  rw [le_div_iff₀ hNE, one_mul, hNG]
  nlinarith

def LatticeIdentityPositive : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ),
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' (ZhatL (lf D F0) F') ∧
    (∀ τ, 0 ≤ Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ)

end Formalism.MainNotions.GramProductBounds

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfCyclic
section
noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Cyc

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def IsCycT (h : V →ₗ⋆[E] V →ₗ[E] E) (T : ℕ) (L : Submodule (𝓞 E) V) : Prop :=
  Submodule.IsLattice E L ∧ IsIntegralLat h L ∧
    ∃ w₁ ∈ dual h L, (∀ w ∈ dual h L, ∃ a : 𝓞 E, w + a • w₁ ∈ L) ∧
      ∀ a : 𝓞 E, a • w₁ ∈ L ↔ ((T : ℕ) : 𝓞 E) ∣ a

theorem cyc_star_int (o : 𝓞 E) : star (algebraMap (𝓞 E) E o) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E o)) :=
    (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩

theorem cyc_natCast_mem_hcompl (p : Ideal (𝓞 E)) (T : ℕ) (hT : ((T : ℕ) : 𝓞 E) ∉ p) :
    ((T : ℕ) : 𝓞 E) ∈ hcompl (K := E) p := by
  unfold hcompl
  apply Submonoid.subset_closure
  refine ⟨hT, fun t ht => ?_⟩
  have e : t = ((T : ℕ) : 𝓞 E) := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [ht, map_natCast, star_natCast]
  rw [e]
  exact hT

theorem cyc_unimodAt (h : V →ₗ⋆[E] V →ₗ[E] E) (T : ℕ) (L : Submodule (𝓞 E) V) (hL : IsCycT h T L)
    (p : Ideal (𝓞 E)) (hTp : ((T : ℕ) : 𝓞 E) ∉ p) : IsUnimodularAt h p L := by
  obtain ⟨hlat, hint, w₁, _, hgen, hann⟩ := hL
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  unfold IsUnimodularAt
  rw [locDual_dualAt_loc h hinj cyc_star_int p L]
  apply le_antisymm
  · refine le_trans (locDual_dualAt_le h cyc_star_int p L hlat.fg) ?_
    intro x hx
    obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
    obtain ⟨a, ha⟩ := hgen _ hsx
    refine locBasic_mem_locS.mpr ⟨((T : ℕ) : 𝓞 E) * s, (hcompl (K := E) p).mul_mem (cyc_natCast_mem_hcompl p T hTp) hs, ?_⟩
    have h1 : (((T : ℕ) : 𝓞 E) * a) • w₁ ∈ L := (hann _).2 (dvd_mul_right _ _)
    have h2 : ((T : ℕ) : 𝓞 E) • (s • x + a • w₁) ∈ L := L.smul_mem _ ha
    have e : (((T : ℕ) : 𝓞 E) * s) • x =
        ((T : ℕ) : 𝓞 E) • (s • x + a • w₁) - (((T : ℕ) : 𝓞 E) * a) • w₁ := by
      rw [smul_add, mul_smul, mul_smul]
      abel
    rw [e]
    exact L.sub_mem h2 h1
  · refine le_trans ?_ (locDual_loc_dual_le h p L)
    intro x hx
    obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
    exact locBasic_mem_locS.mpr ⟨s, hs, (dualBasic_mem_dual h L _).2 fun y hy => hint y hy _ hsx⟩

end Cyc

def CycGenus : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L M : Submodule (𝓞 E) S.V, IsCycT S.hT T L → IsCycT S.hT T M → M ∈ genus S.hT L

def CycSplitAt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L : Submodule (𝓞 E) S.V, IsCycT S.hT T L →
    ∀ p : Ideal (𝓞 E), p.IsMaximal → ((T : ℕ) : 𝓞 E) ∈ p → conjIdeal (K := E) p ≠ p ∧ LocTypeAt S.hT p L

theorem cycGenus_of (hC : CycSplitAt) (hU : LocUnimod) (hS : LocSplitType) : CycGenus := by
  intro F E _ _ _ _ _ _ hc S T hT hT3 hsp L M hL hM
  refine ⟨hM.1, fun p hp => ?_⟩
  by_cases hTp : ((T : ℕ) : 𝓞 E) ∈ p
  · have a := hC F E hc S T hT hT3 hsp L hL p hp hTp
    have b := hC F E hc S T hT hT3 hsp M hM p hp hTp
    exact hS F E hc S L M hL.1 hM.1 hL.2.1 hM.2.1 p hp a.1 a.2 b.2
  · exact hU F E hc S L M hL.1 hM.1 p hp (cyc_unimodAt S.hT T L hL p hTp) (cyc_unimodAt S.hT T M hM p hTp)

section Rows

open Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem row_lattice_cyclic_type (D : D7) (u : D.what₂.Word) (hT : (Tu D u).Prime)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)
    (Λ : LatV D) (hΛr : IsRowLat D F0 Λ) :
    IsCycT (D.sp.X 0).hT (Tu D u) (L0X D Λ (lf D F0)) := by
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hΛr.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hT.ne_zero
  exact ⟨orthLattice_isLattice F0 he hz Λ hΛ hu, orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu, w₁, hw₁, hgen, hann⟩

theorem rows_one_genus_of_cyclic (H : CycGenus) (D : D7) (u : D.what₂.Word) : OrthLatticesOneGenus D u := by
  intro hT hT3 hsp F0 he hz Λ hΛ Λ' hΛ'
  exact H D.host.F D.host.E D.sp.cm (D.sp.X 0) (Tu D u) hT hT3 hsp _ _
    (row_lattice_cyclic_type D u hT F0 he hz Λ hΛ) (row_lattice_cyclic_type D u hT F0 he hz Λ' hΛ')

theorem rows_one_genus_of_local (hC : CycSplitAt) (hU : LocUnimod) (hS : LocSplitType) (D : D7) (u : D.what₂.Word) :
    OrthLatticesOneGenus D u :=
  rows_one_genus_of_cyclic (cycGenus_of hC hU hS) D u

end Rows

end Formalism.MainNotions.BridgeRowsGenus

end
end

