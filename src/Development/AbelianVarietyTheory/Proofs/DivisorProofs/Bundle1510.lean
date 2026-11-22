import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRationalPointTestSupportDoubleCosetsFinit
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.ClsSupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cLoc_mem_UL' (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  by_cases hsp : IsSplitAt w
  · unfold UL; rw [if_pos hsp]; trivial
  · exact GlobalTheory.LocInj.cLoc_mem_UL hsp x

def cw (w : Pl E) : finU E n →* UL n w where
  toFun x := ⟨cLoc w (x : UA E n), cLoc_mem_UL' w _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem toSub_eq (w : Pl E) (x : finU E n) : toSub (UL n w) (cLoc w (x : UA E n)) = cw w x :=
  dif_pos (cLoc_mem_UL' w _)

theorem cw_val (w : Pl E) (x : finU E n) : (cw w x).1 = cLoc w (x : UA E n) := rfl

theorem ne_zero_of_finprod {S : Set (Pl E)} {g : Pl E → ℂ} (hg : ∀ᶠ w in cofinite, g w = 1)
    (h : ∏ᶠ w ∈ S, g w ≠ 0) : ∀ w ∈ S, g w ≠ 0 := by
  intro w₀ hw₀ h₀
  apply h
  rw [finprod_mem_def]
  refine finprod_eq_zero (S.mulIndicator g) w₀ (by rw [Set.mulIndicator_of_mem hw₀, h₀]) ?_
  show (Function.mulSupport _).Finite
  rw [Set.mulSupport_mulIndicator]
  exact (Filter.eventually_cofinite.1 hg).subset Set.inter_subset_right

end GlobalTheory.BCT.ClsSupp

open GlobalTheory.BCT.ClsSupp in

theorem GlobalTheory.BCT.ClsSupp.finite_supp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) (finPt γ) : Set (finU E n)) (globLev S K' : Set (finU E n)) | globFn S f ((Quotient.out q)⁻¹ * finPt γ * (MonoidHom.id (finU E n)) (Quotient.out q)) ≠ 0}.Finite := by
  intro E _ _ _ hU n hn S hS K' hK' f hf γ hγ
  set δ := finPt γ with hδ
  have hych : ∀ w, (cw w δ).1.val.charpoly = atPl w γ.1.val.charpoly := fun w =>
    by rw [cw_val, RegVan.cLoc_finPt_val, Matrix.charpoly_map]
  have hysep : ∀ w, (cw w δ).1.val.charpoly.Separable := fun w => by rw [hych]; exact hγ.map
  have hconj : ∀ (w : Pl E) (x : finU E n),
      cw w (x⁻¹ * δ * (MonoidHom.id (finU E n)) x) = (cw w x)⁻¹ * cw w δ * cw w x := by
    intro w x; simp [map_mul, map_inv]

  have hsupp : ∀ x : finU E n, globFn S f x ≠ 0 → ∀ w ∈ S, f w (cw w x) ≠ 0 := by
    intro x hx
    refine ne_zero_of_finprod (g := fun w => f w (cw w x)) ?_ ?_
    · filter_upwards [RegVan.eventually_toSub_mem x, hf.2] with w a b
      rw [toSub_eq] at a
      rw [b, Set.indicator_of_mem a]; rfl
    · have e : globFn S f x = ∏ᶠ w ∈ S, f w (cw w x) := by
        unfold globFn; simp only [toSub_eq]
      rwa [← e]

  have hinvar : ∀ w, ∀ k ∈ K' w, ∀ z, f w (k⁻¹ * z * k) = f w z := by
    intro w k hk z
    rw [mul_assoc, ((hf.1 w).2 k⁻¹ (inv_mem hk) (z * k)).1, ((hf.1 w).2 k hk z).2]
  have hLfin : ∀ w, {p : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) (cw w δ) : Set (UL n w)) (K' w : Set (UL n w)) |
      (Quotient.out p)⁻¹ * cw w δ * Quotient.out p ∈ tsupport (f w)}.Finite := fun w =>
    (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n w (cw w δ) (hysep w) (K' w) (hK'.1 w)).2 _ (hf.1 w).1.isCompact
  have hloc : ∀ w (g : UL n w), f w (g⁻¹ * cw w δ * g) ≠ 0 →
      (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g))⁻¹ * cw w δ *
        Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g) ∈ tsupport (f w) := by
    intro w g hg
    obtain ⟨h, k, hh, hk, he⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g
    rw [he]
    apply subset_tsupport
    have hh' : h * cw w δ = cw w δ * h := hh
    have e : (h * g * k)⁻¹ * cw w δ * (h * g * k) = k⁻¹ * (g⁻¹ * cw w δ * g) * k := by
      calc (h * g * k)⁻¹ * cw w δ * (h * g * k) = k⁻¹ * (g⁻¹ * (h⁻¹ * (h * cw w δ)) * g) * k := by
            rw [hh']; group
        _ = _ := by rw [inv_mul_cancel_left]
    rw [Function.mem_support, e, hinvar w k hk]; exact hg

  have hgood : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 →
      ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k := by
    filter_upwards [hf.2, hK'.2, RegVan.eventually_toSub_mem δ, GlobalTheory.T.eventually_integralUnitary_conj_of_charpoly_eq E hU n _ hγ] with w hfw hKw hyK hcK
    intro g hg
    rw [hfw] at hg
    have hz : g⁻¹ * cw w δ * g ∈ KL n w := by
      by_contra h; exact hg (Set.indicator_of_notMem h _)
    rw [toSub_eq] at hyK
    have hzc : (g⁻¹ * cw w δ * g).1.val.charpoly = atPl w γ.1.val.charpoly := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
        Matrix.charpoly_units_conj', hych]
    obtain ⟨k, hk, hke⟩ := hcK (cw w δ) _ hyK hz (hych w) hzc
    refine ⟨g * k⁻¹, ?_, k, by rw [hKw]; exact hk, by group⟩
    show g * k⁻¹ * cw w δ = cw w δ * (MonoidHom.id (UL n w)) (g * k⁻¹)
    rw [MonoidHom.id_apply]
    calc g * k⁻¹ * cw w δ = g * (k⁻¹ * cw w δ * k) * k⁻¹ := by group
      _ = g * (g⁻¹ * cw w δ * g) * k⁻¹ := by rw [hke]
      _ = cw w δ * (g * k⁻¹) := by group
  set B : Set (Pl E) := {w | w ∈ S ∧ ¬ ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 →
      ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k} with hBdef
  have hB : B.Finite := (Filter.eventually_cofinite.1 hgood).subset fun w hw => hw.2
  have hBg : ∀ w ∈ S, w ∉ B → ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 →
      ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k := fun w hw hwB =>
    by_contra fun h => hwB ⟨hw, h⟩
  haveI : Finite B := hB.to_subtype
  have hq0 : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) δ : Set (finU E n)) (globLev S K' : Set (finU E n)),
      globFn S f ((Quotient.out q)⁻¹ * δ * (MonoidHom.id (finU E n)) (Quotient.out q)) ≠ 0 → ∀ w ∈ S,
      f w ((cw w (Quotient.out q))⁻¹ * cw w δ * cw w (Quotient.out q)) ≠ 0 := fun q hq w hw => by
    rw [← hconj]; exact hsupp _ hq w hw
  let Φ := fun (q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) δ : Set (finU E n)) (globLev S K' : Set (finU E n)))
      (w : B) => DoubleCoset.mk (twCent (MonoidHom.id (UL n (w : Pl E))) (cw (w : Pl E) δ)) (K' w) (cw (w : Pl E) (Quotient.out q))
  refine Set.Finite.of_finite_image (f := Φ) ?_ ?_
  · refine (Set.Finite.pi fun w : B => hLfin (w : Pl E)).subset ?_
    rintro _ ⟨q, hq, rfl⟩
    exact Set.mem_univ_pi.2 fun w => hloc w _ (hq0 q hq w w.2.1)
  · intro q hq q' hq' he
    have hloc' : ∀ w ∈ S, ∃ t ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w,
        cw w (Quotient.out q') = t * cw w (Quotient.out q) * k := by
      intro w hw
      by_cases hwB : w ∈ B
      · exact (DoubleCoset.eq _ _ _ _).1 (congrFun he ⟨w, hwB⟩)
      · obtain ⟨a, ha, k, hk, hak⟩ := hBg w hw hwB _ (hq0 q hq w hw)
        obtain ⟨a', ha', k', hk', hak'⟩ := hBg w hw hwB _ (hq0 q' hq' w hw)
        refine ⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), k⁻¹ * k', mul_mem (inv_mem hk) hk', ?_⟩
        rw [hak, hak']; group
    have hex : ∀ w : Pl E, ∃ t k : UL n w, t ∈ twCent (MonoidHom.id (UL n w)) (cw w δ) ∧ k ∈ K' w ∧
        (w ∈ S → cw w (Quotient.out q') = t * cw w (Quotient.out q) * k) ∧ (w ∉ S → t = 1) := by
      intro w
      by_cases hw : w ∈ S
      · obtain ⟨t, ht, k, hk, he⟩ := hloc' w hw
        exact ⟨t, k, ht, hk, fun _ => he, fun h => absurd hw h⟩
      · exact ⟨1, 1, one_mem _, one_mem _, fun h => absurd h hw, fun _ => rfl⟩
    choose t k ht hk hte ht1 using hex
    have hKle : ∀ w, K' w ≤ KL n w := fun w => (hK'.1 w).2.1
    have htint : ∀ᶠ w in (cofinite : Filter (Pl E)), t w ∈ KL n w := by
      filter_upwards [RegVan.eventually_toSub_mem (Quotient.out q), RegVan.eventually_toSub_mem (Quotient.out q')]
        with w a b
      rw [toSub_eq] at a b
      by_cases hw : w ∈ S
      · have e : t w = cw w (Quotient.out q') * (k w)⁻¹ * (cw w (Quotient.out q))⁻¹ := by rw [hte w hw]; group
        rw [e]; exact mul_mem (mul_mem b (inv_mem (hKle w (hk w)))) (inv_mem a)
      · rw [ht1 w hw]; exact one_mem _
    obtain ⟨tt, htt⟩ := exists_finU_of_loc E hU n S hS t htint
    obtain ⟨kk, hkk⟩ := exists_finU_of_loc E hU n S hS k (Filter.Eventually.of_forall fun w => hKle w (hk w))
    simp only [toSub_eq] at htt hkk
    have httT : tt ∈ twCent (MonoidHom.id (finU E n)) δ := by
      show tt * δ = δ * (MonoidHom.id (finU E n)) tt
      apply finU_eq_of_loc E hU n S hS
      intro w hw
      have h1 : t w * cw w δ = cw w δ * (MonoidHom.id (UL n w)) (t w) := ht w
      simp only [toSub_eq, MonoidHom.id_apply, map_mul, htt w hw] at h1 ⊢
      exact h1
    have hkkK : kk ∈ globLev S K' := by
      simp only [globLev, Subgroup.mem_iInf]
      intro w hw
      rw [Subgroup.mem_comap]
      exact ⟨k w, hk w, by rw [← hkk w hw]; rfl⟩
    have hgg : Quotient.out q' = tt * Quotient.out q * kk := by
      apply finU_eq_of_loc E hU n S hS
      intro w hw
      simp only [toSub_eq, map_mul, htt w hw, hkk w hw]
      exact hte w hw
    rw [← DoubleCoset.out_eq' (twCent (MonoidHom.id (finU E n)) δ) (globLev S K') q,
      ← DoubleCoset.out_eq' (twCent (MonoidHom.id (finU E n)) δ) (globLev S K') q', DoubleCoset.eq]
    exact ⟨tt, httT, kk, hkkK, hgg⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.LocFin

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem inf_le_cptPart (T K : Subgroup G) (hK : IsCompact (K : Set G)) : T ⊓ K ≤ cptPart T := by
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨hg.1, ?_⟩
  have hzp : (Subgroup.zpowers g : Set G) ⊆ K := (Subgroup.zpowers_le (G := G) (H := K)).2 hg.2
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hzp hK.isClosed)

theorem isCompact_map_conj (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have hc : Continuous fun a : G => x * a * x⁻¹ := by fun_prop
  exact hK.image hc

theorem isOpen_map_conj (K : Subgroup G) (hK : IsOpen (K : Set G)) (x : G) :
    IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  exact (Homeomorph.mulLeft x |>.trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK

theorem relIndex_ne_zero_of_isOpen (A H : Subgroup G) (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G)) :
    A.relIndex H ≠ 0 := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have ho : IsOpen ((A.subgroupOf H : Subgroup H) : Set H) := hA.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_cptPart_ne_zero (T A H : Subgroup G) (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G))
    (hTH : cptPart T ≤ H) : (T ⊓ A).relIndex (cptPart T) ≠ 0 := by
  have hPT : cptPart T ≤ T := by
    rw [cptPart, Subgroup.closure_le]; exact fun t ht => ht.1
  have e : (T ⊓ A) ⊓ cptPart T = A ⊓ cptPart T := by
    ext g; simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hPT h.2, h.1⟩, h.2⟩⟩
  rw [← Subgroup.inf_relIndex_right, e, Subgroup.inf_relIndex_right]
  have h1 := relIndex_ne_zero_of_isOpen A H hA hH
  have : (A.subgroupOf H).FiniteIndex := ⟨h1⟩
  have : Finite (cptPart T ⧸ A.subgroupOf (cptPart T)) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE A hTH).injective
  exact Subgroup.index_ne_zero_of_finite

theorem finite_of_subset_mul (T K' : Subgroup G) (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' T K' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

end Generic

section Main

theorem hKT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := GlobalTheory.T.continuous_involutive_local_transpose_inverse

theorem hKPa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := GlobalTheory.T.orbit_compact_mod_centralizer_separable_local

theorem hKA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := GlobalTheory.T.exists_compact_ge_compactPart_twistedCentralizer

theorem hKPb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := GlobalTheory.T.normCommuting_twistedConj_compact_mem_twistedCentralizer_mul

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twConj (hU : Unr E) (n : ℕ) (w : Pl E) (x y : GLw n w) :
    nrmL n w (x⁻¹ * y * thL n w x) = x⁻¹ * nrmL n w y * x := by
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    simp only [nrmL, if_pos hs, h1, MonoidHom.id_apply]
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have h2 := (hKT E hU n w).2
    rw [h1] at h2
    simp only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]
    group

theorem continuous_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun u => u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have hc := (hKT E hU n w).1
    rw [h1] at hc
    have e : nrmL n w = fun u => u * thetaGL n (cj w) u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id.mul hc

theorem proper (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (C : Set (GLw n w)) (hC : IsCompact C) : ∃ D : Set (GLw n w), IsCompact D ∧
      ∀ x : GLw n w, x⁻¹ * y * thL n w x ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, x = t * d := by
  have hθ := (hKT E hU n w).1
  obtain ⟨D₁, hD₁, h₁⟩ := hKPa E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL hU n w))
  set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)
  have hC₂ : IsCompact C₂ := (hD₁.prod (hC.prod hD₁)).image (by fun_prop)
  obtain ⟨D₂, hD₂, h₂⟩ := hKPb E hU n w y hy C₂ hC₂
  refine ⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩
  intro x hx
  obtain ⟨z, hz, d, hd, rfl⟩ := h₁ x ⟨_, hx, by rw [nrmL_twConj hU]⟩
  have hz2 : z⁻¹ * y * thL n w z ∈ C₂ := ⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by
    simp only [map_mul]; group⟩
  obtain ⟨t, ht, d₂, hd₂, rfl⟩ := h₂ z hz hz2
  exact ⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ K' : Subgroup (GLw n w), IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K' → (∀ x : GLw n w, twCent (thL n w) y ⊓ (GlobalTheory.LFun.KGL w n).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (thL n w) y) ∧ (twCent (thL n w) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (thL n w) y)) ≠ 0) ∧ ∀ C : Set (GLw n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (thL n w) y : Set (GLw n w)) (K' : Set (GLw n w)) | (Quotient.out q)⁻¹ * y * thL n w (Quotient.out q) ∈ C}.Finite := by
  intro E _ _ _ hU n w y hy K' hK'
  obtain ⟨hK'o, hK'K, -⟩ := hK'
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  obtain ⟨H, hH, hPH⟩ := hKA E hU n w y hy
  refine ⟨fun x => ⟨inf_le_cptPart _ _ (isCompact_map_conj _ hKc x),
    relIndex_cptPart_ne_zero _ _ H (isOpen_map_conj _ hK'o x) hH hPH⟩, fun C hC => ?_⟩
  obtain ⟨D, hD, hP⟩ := proper hU n w y hy C hC
  exact finite_of_subset_mul _ K' hK'o D hD _ hP

end Main

end GlobalTheory.LocFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoInvariantFormConstMulInner
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ArchUniq.FormTransport

open GlobalTheory.RealWeil GlobalTheory.ArchUniq
open scoped SchwartzMap ComplexConjugate

theorem rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    rhoFun w G x * conj (rhoFun w G' x) = G (x + pPart w) * conj (G' (x + pPart w)) := by
  have h : phase w x * conj (phase w x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]; simp
  simp only [rhoFun, map_mul]
  calc _ = (phase w x * conj (phase w x)) * (G (x + pPart w) * conj (G' (x + pPart w))) := by ring
    _ = _ := by rw [h, one_mul]

theorem integral_rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w G x * conj (rhoFun w G' x) = ∫ x, G x * conj (G' x) := by
  simp_rw [rhoFun_mul_conj]
  exact integral_add_right_eq_self (fun x => G x * conj (G' x)) (pPart w)

open scoped Classical in

theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    {κ : Type} [Fintype κ] (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (u : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w u = schrF (trP F κ) w u := by
  funext x
  have h2 : (⅟(2 : mixedEmbedding.mixedSpace F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]
    norm_num
  have ht : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ w.2 + ⅟(2 : mixedEmbedding.mixedSpace F) * (w.1 ⬝ᵥ w.2)) =
      trP F κ x w.2 + trP F κ w.1 w.2 / 2 := by
    rw [map_add, h2, ← Algebra.smul_def, map_smul, smul_eq_mul]
    simp only [trP, dotProduct]
    ring
  simp only [schr, schrF, hψ, ht]

theorem haar_coords_cplx {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, ∀ G : V → ℂ, ∫ y, G y ∂μ = (k : ℂ) * ∫ x, G (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ), fun G => ?_⟩
  have h1 : ∫ y, G y ∂μ = ∫ x, G (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, G (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

open scoped Classical in

theorem const_of_euclidean : (∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x)) → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  intro H F _ _ _ κ _ ψ hψ T A hT
  letI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  have hP : IsPairing (trP F κ) := Coord.isPairing_trP κ
  obtain ⟨C, φ, -, hS⟩ := exists_pairing_coords (κ → mixedEmbedding.mixedSpace F) (trP F κ) hP _ rfl
  generalize Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F) = n at C φ hS
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  let T' : Sch (Fin n) →L[ℂ] Sch (Fin n) := toE.comp (T.comp toV)
  have hT' : ∀ h, T' h = toE (T (toV h)) := fun h => rfl
  have hI : ∀ w (h g : Sch (Fin n)), ⇑g = rhoFun w ⇑h → ⇑(T' g) = rhoFun (φ (A (φ.symm w))) ⇑(T' h) := by
    intro w h g hg
    have e1 : ⇑(toV g) = schr ψ (φ.symm w) ⇑(toV h) := by
      rw [schr_eq_schrF ψ hψ]
      funext x
      have := congrFun (hS (φ.symm w) ⇑h) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hg]
      exact this.symm
    have e2 := hT _ _ _ e1
    rw [schr_eq_schrF ψ hψ] at e2
    rw [hT', hT', htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T (toV h)) = G ∘ ⇑C :=
      ⟨⇑(T (toV h)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp
  let B : Sch (Fin n) → Sch (Fin n) → ℂ := fun h h' => ∫ x, T' h x * conj (T' h' x)
  have hcont : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h := by
    intro h'
    refine ⟨(innerSL ℂ ((T' h').toLp 2)).comp
      ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))).comp T'), fun h => ?_⟩
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.inner_toL2_toL2_eq (T' h') (T' h) volume]
    simp only [B, RCLike.inner_apply]
  have hherm : ∀ h h', B h' h = conj (B h h') := by
    intro h h'
    simp only [B]
    rw [← integral_conj]
    congr 1
    funext x
    simp [mul_comm]
  have hpos : ∀ h, 0 ≤ (B h h).re := by
    intro h
    have e : B h h = ((∫ x, Complex.normSq (T' h x) : ℝ) : ℂ) := by
      have e0 : B h h = ∫ x, ((Complex.normSq (T' h x) : ℝ) : ℂ) := by simp only [B, Complex.mul_conj]
      rw [e0]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [e, Complex.ofReal_re]
    exact integral_nonneg fun x => Complex.normSq_nonneg _
  have hinv : ∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : Sch (Fin n)), ⇑g = rhoFun w ⇑h →
      ⇑g' = rhoFun w ⇑h' → B g g' = B h h' := by
    intro w h h' g g' hg hg'
    simp only [B]
    rw [hI w h g hg, hI w h' g' hg']
    exact integral_rhoFun_mul_conj _ _ _
  obtain ⟨c, hc0, hc⟩ := H n B hcont hherm hpos hinv
  have hB : ∀ f f' : SInf F κ, ∫ x, T f (C.symm x) * conj (T f' (C.symm x)) =
      (c : ℂ) * ∫ x, f (C.symm x) * conj (f' (C.symm x)) := by
    intro f f'
    have := hc (toE f) (toE f')
    simpa only [B, hT', hVE, htoE, Function.comp_apply] using this
  refine ⟨c, hc0, fun μ hμ f f' => ?_⟩
  haveI := hμ
  obtain ⟨k, hk⟩ := haar_coords_cplx μ C
  rw [hk, hk, hB]
  ring

end GlobalTheory.ArchUniq.FormTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetArchimedeanNormBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_archimedean_norm_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E) (c : ℝ), 0 < c →
    ∃ (C : ℝ) (A : ℕ), ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ a : GAd σ J, a ∈ infPts σ J →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w),
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1)) →
      (height σ J a : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  first | exact @GlobalTheory.TorusHeight.height_torus_le | exact GlobalTheory.TorusHeight.height_torus_le | (intros; apply GlobalTheory.TorusHeight.height_torus_le <;> assumption)
end

