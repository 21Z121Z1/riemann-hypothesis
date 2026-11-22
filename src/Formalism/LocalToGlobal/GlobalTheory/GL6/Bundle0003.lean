import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedRankEqFinrank
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0006
import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionFamilyOf

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfHeckeRamified
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

section Min

variable (D : D7) (u : D.what₂.Word)

def HeckeIntegralLevelZero : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    Into D u w (Uop D u 0 v) ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) ∧
    Into D u w (Dop D u 0 v) ((D.fm u).S 0 w) ((D.fm u).Bw 0 w v)

def HeckeRamifiedLevelZero : Prop :=
  ∀ v, ∀ φ ∈ MramI D u 0, Uop D u 0 v φ ∈ MramI D u 0 ∧ Dop D u 0 v φ ∈ MramI D u 0 ∧
    Uop D u 0 v (Dop D u 0 v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ

def SecondBranchInclusionLength : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ)))

variable {D u}

theorem secondBranchInclusionLength_of_lemB (hB : LemB D u) : SecondBranchInclusionLength D u := by
  unfold LemB at hB
  intro w hw hs v hb
  exact (hB w hw hs v).2 hb

theorem rational_level_zero_of_integral (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true) (h4 : HeckeIntegralLevelZero D u) :
    Rat0 D u := fun v =>
  ⟨rat_of_into w _ _ _ (h4 w hw hs v).1 ((D.fm u).Bw_span 0 w v),
    rat_of_into w _ _ _ (h4 w hw hs v).2 (S_span 0 w)⟩

theorem hecke_ramified_lattice_stable_length (hS : HidaSetting D u) (hR : Rat0 D u) (hB : SecondBranchInclusionLength D u) (h4 : HeckeIntegralLevelZero D u) (h9 : HeckeRamifiedLevelZero D u)
    (w : D.what₂.places.Pl) (hw : OverT D u w) {v : (D.mem u).A.vT} (hv : v ∈ VV D u w) :
    (Sram D u w).map (gR hR w v) ≤ Sram D u w ∧
    ∃ n : ℕ, (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ)) ∧
      Module.length (Ow D w) (Sram D u w ⧸ ((Sram D u w).map (gR hR w v)).comap (Sram D u w).subtype) ≤
        ((n + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) := by
  obtain ⟨hs, ht⟩ := mem_VV hv
  have hb : 0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) := hS.2.2 _ ht
  have hnb : ((nb D u w v : ℕ) : ℤ) = (D.fm u).bTop ((D.fm u).tauOf w v) := Int.toNat_of_nonneg hb
  obtain ⟨hUB, hDS⟩ := h4 w hw hs v
  obtain ⟨a1, n, a2, a3⟩ := hB w hw hs v hb
  rw [← hnb, tL_eq_map] at a1 a2
  have ram := h9 v
  refine ⟨?_, n, a3, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxB : (((D.mem u).A.T : ℕ) : Ow D w) ^ nb D u w v • x ∈ (D.fm u).Bw 0 w v := a1 ⟨x, hx.1, rfl⟩
    obtain ⟨y, hy, hy'⟩ := hUB _ hxB
    have e : gR hR w v x = y := by
      apply (D.fm u).emb_inj 0
      rw [hy', gR_spec, emb_smulR, map_smul]; simp
    rw [e]
    refine ⟨hy, mem_ramSub.mpr ?_⟩
    rw [← e, gR_spec]
    exact Submodule.smul_mem _ _ (ram _ (mem_ramSub.mp hx.2)).1
  · have h := LemmaC_core hR w hw v (nb D u w v) (fun x hx => a1 ⟨x, hx, rfl⟩) hUB hDS ram
    unfold len at a2
    rw [a2] at h
    exact_mod_cast h

theorem congruence_no_kernel_minimal (hS : HidaSetting D u) (hB : SecondBranchInclusionLength D u) (h4 : HeckeIntegralLevelZero D u) (h9 : HeckeRamifiedLevelZero D u) :
    CongruenceLatticeLengthBound D u := by
  intro w hw
  by_cases hs : (D.fm u).seenP w = true
  · have hR : Rat0 D u := rational_level_zero_of_integral w hw hs h4
    have hg : ∀ v ∈ (VV D u w).toList, (Sram D u w).map (gR hR w v) ≤ Sram D u w :=
      fun v hv => (hecke_ramified_lattice_stable_length hS hR hB h4 h9 w hw (Finset.mem_toList.mp hv)).1
    obtain ⟨hG, hGl⟩ := len_list_le (Sram D u w) (gR hR w) (VV D u w).toList hg
    obtain ⟨hP, hPl⟩ := len_pow_le (Sram D u w) (GR hR w (VV D u w).toList) hG D.R.m
    rw [Nlam_eq hS hR w]
    refine ⟨hP, ?_⟩
    have H : ∀ v : {v // v ∈ VV D u w}, ∃ n : ℕ, (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℚ) +
            (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℚ)) / (D.R.k : ℚ)) ∧
        Module.length (Ow D w) (Sram D u w ⧸ ((Sram D u w).map (gR hR w v.1)).comap (Sram D u w).subtype) ≤
          ((n + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) :=
      fun v => (hecke_ramified_lattice_stable_length hS hR hB h4 h9 w hw v.2).2
    choose nn hnq hnl using H
    have hsum : Module.length (Ow D w) (Sram D u w ⧸
        ((Sram D u w).map (GR hR w (VV D u w).toList ^ D.R.m)).comap (Sram D u w).subtype) ≤
        ((D.R.m * ∑ v ∈ (VV D u w).attach, (nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u)) : ℕ) : ℕ∞) := by
      refine le_trans hPl ?_
      push_cast
      rw [nsmul_eq_mul]
      refine mul_le_mul_right (le_trans hGl ?_) _
      rw [Finset.sum_map_toList, ← Finset.sum_attach]
      exact Finset.sum_le_sum (fun v _ => by exact_mod_cast hnl v)
    obtain ⟨n, hn, hle⟩ := ENat.le_natCast_iff.mp hsum
    refine ⟨n, hn, ?_⟩
    have hk : (0 : ℝ) < (D.R.k : ℝ) := by
      have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 0 < D.R.k)
    have he : (0 : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
    have hterm : ∀ v : {v // v ∈ VV D u w},
        ((nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℝ) ≤
          (D.what₂.places.ramIdx w : ℝ) * (D.duS u * ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1) + D.R.k +
            (D.fm u).bTop ((D.fm u).tauOf w v.1))) := by
      intro v
      have ht := (mem_VV v.2).2
      have hb : 0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v.1) := hS.2.2 _ ht
      have hbR : (0 : ℝ) ≤ ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ) := by exact_mod_cast hb
      have hN1 := twist_le (u := u) ht
      have hq : ((nn v : ℕ) : ℝ) = (D.what₂.places.ramIdx w : ℝ) * ((D.duS u : ℝ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℝ) +
            (D.R.k : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ)) / (D.R.k : ℝ)) := by
        have := congrArg (fun q : ℚ => (q : ℝ)) (hnq v)
        push_cast at this; exact this
      have hk1 : ((D.R.k - 1 : ℕ) : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Nat.sub_le _ _
      push_cast
      rw [hq, mul_div_assoc, ← mul_add]
      apply mul_le_mul_of_nonneg_left _ he
      have e1 : (D.duS u : ℝ) * (((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℝ) +
            (D.R.k : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ)) / (D.R.k : ℝ)) ≤
          (D.duS u : ℝ) * ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1)) :=
        mul_le_mul_of_nonneg_left hN1 hd
      have e2 : ((D.R.k - 1 : ℕ) : ℝ) * (D.duS u : ℝ) ≤ (D.duS u : ℝ) * (D.R.k : ℝ) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hk1 hd
      have e3 : 0 ≤ (D.duS u : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ) := mul_nonneg hd hbR
      nlinarith
    calc (n : ℝ) ≤ ((D.R.m * ∑ v ∈ (VV D u w).attach,
            (nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u)) : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (D.R.m : ℝ) * ∑ v ∈ (VV D u w).attach,
            ((nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (D.R.m : ℝ) * ∑ v ∈ (VV D u w).attach, ((D.what₂.places.ramIdx w : ℝ) * (D.duS u *
            ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1) + D.R.k +
              (D.fm u).bTop ((D.fm u).tauOf w v.1)))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hterm v)) (Nat.cast_nonneg _)
      _ = _ := by
          rw [Finset.sum_attach (VV D u w) (fun v => (D.what₂.places.ramIdx w : ℝ) * (D.duS u *
            ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v) + D.R.k +
              (D.fm u).bTop ((D.fm u).tauOf w v)))), ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  · have hs' : (D.fm u).seenP w = false := by simpa using hs
    have hVV : VV D u w = ∅ := by simp [LT.VVT, hs']
    have hN : Nlam D u w = Sram D u w := by
      have := imgL_eq_map (u := u) w ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (Uprod D u 0 w) ^ D.R.m) LinearMap.id
        (fun x => by simp [LT.expT, LT.Uprod, LT.VVT, hs']) (Sram D u w)
      rw [Submodule.map_id] at this
      exact this
    rw [hN, hVV]
    refine ⟨le_rfl, 0, ?_, by simp⟩
    unfold len
    rw [Submodule.comap_subtype_self]
    simp

theorem congruence_no_kernel_family_minimal
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → admS D u →
      HeckeIntegralLevelZero D u ∧ HeckeRamifiedLevelZero D u ∧ SecondBranchInclusionLength D u) : CongruenceLatticeLengthBoundFamily := fun D u hF hS hA =>
  have h' := h D u hF hS hA
  congruence_no_kernel_minimal hS h'.2.2 h'.1 h'.2.1

end Min

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondPreservesForms
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem diamond_preserves_forms (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hφ : φ ∈ (D.fm u).Fi i) :
    Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ∈ (D.fm u).Fi i := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi).Fi φ).1 hφ
  have hval : ∀ c, φ c = fun z => g ((Tf.cls i hi).y c) ((Tf.val i hi).eY z) := by
    intro c; funext z
    have := congrFun (congrFun hgφ c) ((Tf.val i hi).eY z)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hgA : g ∈ AdFun (Tf.cls i hi).lev (embT D) := (Submodule.mem_inf.1 hg).1
  have hgV := Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2
  obtain ⟨k, hk, δ, hδ⟩ := hE i hi v a
  have hg' := adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) _ _ (level_places_not_bad Tf.atT v) hδ hgA
  refine ((Tf.val i hi).Fi _).2 ⟨fun x => g (x * δ), Submodule.mem_inf.2 ⟨hg', Submodule.mem_pi.2
    (fun x _ => hgV (x * δ) (Set.mem_univ _))⟩, ?_⟩
  funext c z
  show g ((Tf.cls i hi).y c * δ) z = (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) ((Tf.val i hi).eY.symm z)
  rw [hval, (Tf.val i hi).dilT v a k hk c δ hδ g hgA]
  simp only [Equiv.apply_symm_apply]

theorem diamond_comm_same_place (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (a b : ((D.mem u).A.Fv v)ˣ) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hφ : φ ∈ (D.fm u).Fi i) :
    Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ) = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) := by
  have hM := diamond_mul_of_diamond_elements Tf hE
  rw [← (hM i hi v φ hφ).2 a b, ← (hM i hi v φ hφ).2 b a, mul_comm]

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.ExistsIntegerSmulMemOfSpanTop
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions NumberField Matrix

theorem exists_integer_smul_mem_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • x ∈ L :=
  _root_.UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top L hL x

variable (D : D7) (u : D.what₂.Word)

theorem norm_preserves_rational_form (v : (D.mem u).A.vT) (x : ((D.fm u).lat 0).V) :
    ∃ y, (D.fm u).emb 0 y = (D.mem u).A.Nm v ((D.fm u).emb 0 x) := by
  have hL : ∀ x ∈ ((D.fm u).lat 0).L, ∃ y, (D.fm u).emb 0 y = (D.mem u).A.Nm v ((D.fm u).emb 0 x) := by
    intro x hx
    choose ys _ hys using fun a => (D.fm u).rhoT_lat v a x hx
    refine ⟨∑ a, ys a, ?_⟩
    rw [map_sum]
    unfold ColumnsAtT.Nm
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hys a
  obtain ⟨r, hr, hrx⟩ := exists_integer_smul_mem_of_span_top ((D.fm u).lat 0).L ((D.fm u).lat_good 0).2.2 x
  obtain ⟨y, hy⟩ := hL _ hrx
  have hrK : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL)]; exact hr
  refine ⟨(algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ • y, ?_⟩
  rw [LinearMap.map_smulₛₗ, hy, ← algebraMap_smul D.what₂.LL r x, LinearMap.map_smulₛₗ, map_smul, smul_smul,
    ← map_mul, inv_mul_cancel₀ hrK, map_one, one_smul]

theorem ramified_rational_ne_bot (h : (D.mem u).A.Mram ≠ ⊥) : (D.fm u).ramSub ≠ ⊥ := by
  classical
  choose yv hyv using fun v j => norm_preserves_rational_form D u v (((D.fm u).lat 0).b j)
  let A : Matrix ((D.mem u).A.vT × ((D.fm u).lat 0).ι) ((D.fm u).lat 0).ι D.what₂.LL :=
    fun p j => ((D.fm u).lat 0).b.repr (yv p.1 j) p.2
  have hE : ∀ x : ((D.fm u).lat 0).V, (D.fm u).emb 0 x =
      ∑ i, D.what₂.embLL (((D.fm u).lat 0).b.repr x i) • (D.fm u).emb 0 (((D.fm u).lat 0).b i) := by
    intro x
    conv_lhs => rw [← ((D.fm u).lat 0).b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ _ _ _
  have key : ∀ (v : (D.mem u).A.vT) (c : ((D.fm u).lat 0).ι → ℂ),
      (D.mem u).A.Nm v (∑ j, c j • (D.fm u).emb 0 (((D.fm u).lat 0).b j)) =
        ∑ i, ((A.map D.what₂.embLL) *ᵥ c) (v, i) • (D.fm u).emb 0 (((D.fm u).lat 0).b i) := by
    intro v c
    rw [map_sum]
    have hj : ∀ j, (D.mem u).A.Nm v (c j • (D.fm u).emb 0 (((D.fm u).lat 0).b j)) =
        c j • ∑ i, D.what₂.embLL (((D.fm u).lat 0).b.repr (yv v j) i) • (D.fm u).emb 0 (((D.fm u).lat 0).b i) := by
      intro j; rw [map_smul, ← hyv, ← hE (yv v j)]
    rw [Finset.sum_congr rfl fun j _ => hj j]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hli := ((D.fm u).emb_basis 0).1
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hzMu : z ∈ (D.mem u).A.Mu0 := hz.1
  rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2] at hzMu
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hzMu
  have hc0 : c ≠ 0 := by
    rintro rfl; apply hz0; rw [← hc]; simp
  have hAc : (A.map D.what₂.embLL) *ᵥ c = 0 := by
    funext p
    obtain ⟨v, i⟩ := p
    have hv : (D.mem u).A.Nm v z = 0 := by
      have : z ∈ ⨅ v, LinearMap.ker ((D.mem u).A.Nm v) := hz.2
      rw [Submodule.mem_iInf] at this; exact this v
    rw [← hc, key] at hv
    exact (Fintype.linearIndependent_iff.1 hli) _ hv i
  have hx : ∃ x : ((D.fm u).lat 0).ι → D.what₂.LL, x ≠ 0 ∧ A *ᵥ x = 0 := by
    by_contra hne
    push Not at hne
    have hker : LinearMap.ker A.mulVecLin = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx; by_contra hx0; exact hne x hx0 hx
    obtain ⟨g, hg⟩ := A.mulVecLin.exists_leftInverse_of_injective hker
    have hBA : LinearMap.toMatrix' g * A = 1 := by
      have h1 := congrArg LinearMap.toMatrix' hg
      rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h1
    have hBA' : (LinearMap.toMatrix' g).map D.what₂.embLL * A.map D.what₂.embLL = 1 := by
      rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero _) (map_one _)]
    apply hc0
    rw [← Matrix.one_mulVec c, ← hBA', ← Matrix.mulVec_mulVec, hAc, Matrix.mulVec_zero]
  obtain ⟨x, hx0, hAx⟩ := hx
  have hX0 : ∑ j, x j • ((D.fm u).lat 0).b j ≠ 0 := by
    intro h0
    exact hx0 (funext fun j => (Fintype.linearIndependent_iff.1 ((D.fm u).lat 0).b.linearIndependent) x h0 j)
  have hEX : (D.fm u).emb 0 (∑ j, x j • ((D.fm u).lat 0).b j) =
      ∑ j, (D.what₂.embLL ∘ x) j • (D.fm u).emb 0 (((D.fm u).lat 0).b j) := by
    rw [map_sum]; exact Finset.sum_congr rfl fun j _ => LinearMap.map_smulₛₗ _ _ _
  refine Submodule.ne_bot_iff _ |>.2 ⟨_, ?_, hX0⟩
  show (D.fm u).emb 0 (∑ j, x j • ((D.fm u).lat 0).b j) ∈ (D.mem u).A.Mram
  rw [hEX]
  refine ⟨?_, ?_⟩
  · rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · show _ ∈ ⨅ v, LinearMap.ker ((D.mem u).A.Nm v)
    rw [Submodule.mem_iInf]
    intro v
    rw [LinearMap.mem_ker, key]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ((A.map D.what₂.embLL) *ᵥ (D.what₂.embLL ∘ x)) (v, i) = 0 := by
      rw [← RingHom.map_mulVec, hAx, Pi.zero_apply, map_zero]
    rw [this, zero_smul]

theorem ramified_lattice_ne_bot (h : (D.mem u).A.Mram ≠ ⊥) : (D.fm u).ramL ≠ ⊥ := by
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ramified_rational_ne_bot D u h)
  obtain ⟨r, hr, hrX⟩ := exists_integer_smul_mem_of_span_top ((D.fm u).lat 0).L ((D.fm u).lat_good 0).2.2 X
  have hrK : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL)]; exact hr
  refine Submodule.ne_bot_iff _ |>.2 ⟨r • X, ⟨hrX, ?_⟩, ?_⟩
  · show r • X ∈ (D.fm u).ramSub
    rw [← algebraMap_smul D.what₂.LL r X]
    exact (D.fm u).ramSub.smul_mem _ hX
  · rw [← algebraMap_smul D.what₂.LL r X]
    exact smul_ne_zero hrK hX0

theorem ramified_forms_ne_bot (M : FreeRankModel (D.mem u).A) (hT : 3 ≤ (D.mem u).A.T) (hd : 0 < D.duS u) :
    (D.mem u).A.Mram ≠ ⊥ := by
  intro h0
  have hdu : (D.mem u).A.du = 0 := by
    unfold ColumnsAtT.du; rw [h0, finrank_bot]
  have h := ramified_rank_mul (D.mem u).A M
  rw [hdu, zero_mul] at h
  have hpos : 0 < (D.duS u) * ((D.mem u).A.T - 2) ^ D.R.f := Nat.mul_pos hd (Nat.pow_pos (by omega))
  unfold D7.duS at hpos
  omega

theorem ramified_max_slope_le_of_model (M : FreeRankModel (D.mem u).A) (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (hd : 0 < D.duS u) :
    (D.fm u).ramLat.muMax ≤ ((D.fm u).lat 0).muMax := by
  have hT : 3 ≤ (D.mem u).A.T := by
    have h1 : 1 ≤ D.R.f := by
      have h0 : 0 < D.R.n := D.R.toFrame.ord_pos
      have hf : D.R.f = 2 * D.R.n := rfl
      omega
    have h2 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
    have h3 : 1 ≤ D.R.f * D.R.N D.R.m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have := hS.1
    have h4 : 2 * D.R.f * D.R.N D.R.m = 2 * (D.R.f * D.R.N D.R.m) := by ring
    omega
  exact ramified_max_slope_le D u (ramified_lattice_ne_bot D u (ramified_forms_ne_bot D u M hT hd))

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionOfSubIntegral
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

def bwA_N {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => if τ = τv then atInf (embT D) (B'⁻¹ * B : GL (Fin n) D.host.E).1 τ else 1

theorem bwA_N_mul {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    (fun τ => bwA_N D τv B B' τ * atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ) =
      fun τ => if τ = τv then atInf (embT D) (B'⁻¹ : GL (Fin n) D.host.E).1 τ
        else atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ := by
  funext τ
  unfold bwA_N
  split_ifs with h
  · simp only [atInf]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  · rw [one_mul]

def BwLocBases (Tt : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i),
    (∃ B : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B) ∧
    ∀ v, ∃ B' : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B'

def BwSubInt (Tt : FormsTied D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
    ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B →
      IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B' →
      ∀ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i),
        tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) •
          (MvPolynomial.C (∏ τ, (bwA_N D ((D.fm u).tauOf w v) B B' τ).det ^ shiftOf (lamT u i) τ) *
            subP (bwA_N D ((D.fm u).tauOf w v) B B') P) ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i)

def BwLocGlob (Tt : FormsTied D u) : Prop :=
  ∀ w, OverT D u w → ∀ i (hi : i ≤ D.R.m) (y : ((D.fm u).lat i).V),
    (∀ c, ∃ B : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B ∧
      ∃ Q ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∀ z, (D.fm u).emb i y c z =
        fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q ((Tt.val i hi).eY z)) →
    y ∈ (D.fm u).S i w

theorem bwA_bwIncl_of (Tt : FormsTied D u) (h1 : BwLocBases D u Tt) (h2 : BwSubInt D u Tt)
    (h3 : BwLocGlob D u Tt) : BwIncl D u := by
  intro w hw i hi hs v hv x hx
  apply h3 w hw i hi
  intro c
  obtain ⟨⟨B, hB⟩, hB'⟩ := h1 i hi c
  obtain ⟨B', hB'⟩ := hB' v
  obtain ⟨P, hP, hxP⟩ := ((Tt.bw i hi) w hw hs v x).1 hx c B B' hB hB'
  refine ⟨B, hB, _, h2 w hw hs v hv i hi c B B' hB hB' P hP, fun z => ?_⟩
  rw [emb_tpow_smul, Pi.smul_apply, Pi.smul_apply, hxP z, ← bwA_N_mul, fnOf_mul, LinearMap.map_smul]
  rfl

theorem lattice_inclusion_of_sub_integral
    (h1 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwLocBases D u Tt)
    (h2 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwSubInt D u Tt)
    (h3 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwLocGlob D u Tt) : WeightLatticeInclusionFamily :=
  lattice_inclusion_family_of fun D u hT _ => by
    obtain ⟨Tt, _⟩ := hT
    exact bwA_bwIncl_of D u Tt (h1 D u Tt) (h2 D u Tt) (h3 D u Tt)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

