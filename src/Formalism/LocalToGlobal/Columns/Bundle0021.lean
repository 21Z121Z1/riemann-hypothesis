import Formalism.LocalToGlobal.Columns.Bundle0013
import Formalism.LocalToGlobal.Columns.Record
import Formalism.LocalToGlobal.Columns.TiedGlLoc
import Formalism.LocalToGlobal.Columns.LevGCount

-- bundled from Formalism.LocalToGlobal.Columns.RecLevelSymExt
section
noncomputable section

open NumberField IsDedekindDomain Matrix

namespace Formalism.L2.Col

open Formalism.BasicNotions (Ranks)

section SymExt

variable {κ : Type} [CommRing κ]

theorem symX_padM_eq {n : ℕ} (h : GL (Fin n) κ) : Units.map (padM κ n) h = diagEmb κ (Nat.le_succ n) h := by
  apply Units.ext
  ext i j
  rw [diagEmb_val]
  show padM κ n h.1 i j = diagMat n (n + 1) h.1 i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
  · rw [diagMat_of_not_left _ _ (by simp)]
    simp [padM]
  · rw [diagMat_of_not_left _ _ (by simp)]
    simp [padM, (Fin.castSucc_ne_last _).symm]
  · rw [diagMat_of_not_right _ _ (by simp)]
    simp [padM, Fin.castSucc_ne_last]
  · rw [diagMat_of_lt _ (show (Fin.castSucc i').val < n from i'.2) (show (Fin.castSucc j').val < n from j'.2)]
    simp [padM]

theorem diagEmb_mem_HXmsym {n' k r t m rS : ℕ} (hn : n' = r + m * t) (hr : r ≤ n') (hrN : r ≤ n' + 1) (g : GL (Fin n') κ)
    (hg : g ∈ HJsym κ n' k r t m rS hr) : diagEmb κ (Nat.le_succ n') g ∈ HXmsym κ (n' + 1) k r t m rS hrN := by
  obtain ⟨hB, h0⟩ := mem_HPar.mp hg
  have hB' : diagEmb κ (Nat.le_succ n') g ∈ blockUT (n' + 1) κ r (List.replicate m t) := by
    refine mem_btG.mpr fun i j hij => ?_
    rw [diagEmb_val]
    by_cases hi : i.val < n'
    · by_cases hj : j.val < n'
      · rw [diagMat_of_lt _ hi hj]
        exact (mem_btG.mp hB) ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
      · exfalso
        have := blkIdx_mono (r :: List.replicate m t) (show i.val ≤ j.val by omega)
        unfold coarse at hij
        omega
    · rw [diagMat_of_not_left _ _ hi]
      exact Matrix.one_apply_ne (fun e => by rw [e] at hij; omega)
  refine ⟨mem_HPar.mpr ⟨hB', ?_⟩, ?_⟩
  · have e : blk0 (n' + 1) κ hrN (List.replicate m t) ⟨diagEmb κ (Nat.le_succ n') g, hB'⟩ =
        blk0 n' κ hr (List.replicate m t) ⟨g, hB⟩ := by
      apply Units.ext
      ext a b
      rw [blockZero_val, blockZero_val]
      show (diagEmb κ (Nat.le_succ n') g : Matrix (Fin (n' + 1)) (Fin (n' + 1)) κ) (Fin.castLE hrN a) (Fin.castLE hrN b) =
        (g : Matrix (Fin n') (Fin n') κ) (Fin.castLE hr a) (Fin.castLE hr b)
      rw [diagEmb_val, diagMat_of_lt _ (show (Fin.castLE hrN a).val < n' by simp; omega)
        (show (Fin.castLE hrN b).val < n' by simp; omega)]
      rfl
    rw [e]
    exact h0
  · intro i j hj
    rw [diagEmb_val, diagMat_of_not_right _ _ (by omega)]

theorem symX_ext_mem {E : Type} [Field E] [NumberField E] [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))} {N n : ℕ}
    (hN : N = n + 1) (k r t m rS : ℕ) (hn : n = r + m * t) (hr : r ≤ n) (hrN : r ≤ N) (g : GLG E n SG) (w : SG)
    (hg : g w ∈ HJsym (𝓞 E ⧸ w.1.asIdeal) n k r t m rS hr) :
    extGH hN g w ∈ HXmsym (𝓞 E ⧸ w.1.asIdeal) N k r t m rS hrN := by
  subst hN
  have := diagEmb_mem_HXmsym hn hr hrN (g w) hg
  rw [← symX_padM_eq] at this
  exact this

end SymExt

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlCore
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))
  (w : Pl E) (hw : ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0)

theorem gco_red_map {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    ((redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w ⟨k, hk⟩ : GL (Fin n) (kP w)) : Matrix (Fin n) (Fin n) (kP w)).map
        (gloE v spl halg w hw) =
      redM F v ((bc (gloPhi v spl) (bc (prV (E := E) v) k) : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  obtain ⟨y, hy, hr⟩ := St_one_int hk
  ext i j
  rw [Matrix.map_apply, hr w i j, gloE_resS, gloRho_apply]
  have e : ((bc (gloPhi v spl) (bc (prV (E := E) v) k) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = gloPhi v spl (prV (E := E) v (y i j : E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [← hy i j]; rfl
  unfold redM
  have hm : ((bc (gloPhi v spl) (bc (prV (E := E) v) k) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    rw [e]; exact gloPhi_int v spl halg _ (afsplit_prV_int v _ (y i j).2)
  rw [dif_pos hm]
  congr 1
  exact Subtype.ext e.symm

variable (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))

theorem gco_mem_levLoc (w : SG) (hw : ∀ a ∈ w.1.asIdeal, gloRho v spl halg (oToS F E a) = 0) (hov : IsOver v w.1)
    (huniq : ∀ w' : SG, IsOver v w'.1 → w' = w) (hT : v ∉ plUnder F ST)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) :
    x ∈ levLoc hc n ST SG (Subgroup.pi Set.univ Hw) v ↔
      ∃ M ∈ Hw w, (M : Matrix (Fin n) (Fin n) (kP w.1)).map (gloE v spl halg w.1 hw) =
        redM F v ((bc (gloPhi v spl) x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hJ, hred⟩ := (mem_levU hc n ST SG _).1 hk
    exact ⟨_, hred w (Set.mem_univ w), gco_red_map n v spl halg w.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)⟩
  · rintro ⟨M, hM, hMx⟩
    have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
    have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
      rw [← rll_locL_base n ST v hT]; exact hx.2
    have hS := rll_put_mem_St n v hxS
    have hJ : rll_put n v x ∈ J0 hc n ST := by
      refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hxU, hS, fun P hP => ?_⟩
      rw [rll_put_red n v x hS P (fun h => hT ⟨P, hP, h⟩)]
      exact Subgroup.one_mem _
    refine ⟨rll_put n v x, (mem_levU hc n ST SG _).2 ⟨hJ, ?_⟩, rll_put_self n v x⟩
    intro w' _
    show redAt 1 w'.1 ⟨rll_put n v x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ ∈ Hw w'
    by_cases hw' : IsOver v w'.1
    · obtain rfl := huniq w' hw'
      have h1 := gco_red_map n v spl halg w'.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)
      rw [rll_put_self, ← hMx] at h1
      have h2 : redAt 1 w'.1 ⟨rll_put n v x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ = M := by
        apply Units.ext
        ext i j
        have := congrFun (congrFun h1 i) j
        rw [Matrix.map_apply, Matrix.map_apply] at this
        exact (gloE v spl halg w'.1 hw).injective this
      rw [h2]; exact hM
    · rw [rll_put_red n v x _ w'.1 hw']
      exact Subgroup.one_mem _

include halg in

theorem gco_fr_lat (hT : v ∉ plUnder F ST) (x : Fin n → v.adicCompletion F) :
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST), ∀ b, gloPhi v spl (y b) = x b) ↔
      ∀ b, (((1 : GL (Fin n) (v.adicCompletion F))⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F := by
  have hL : latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST) =
      Formalism.UG.stdLat (n := Fin n) (A := E ⊗[F] v.adicCompletion F) (Formalism.BasicNotions.intV E v) :=
    (rll_locL_base n ST v hT).trans (rll_locL_std n v)
  rw [hL, inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · rintro ⟨y, hy, hyx⟩ b
    rw [← hyx b]
    exact gloPhi_int v spl halg _ ((afsplit_mem_stdLat _ y).1 hy b)
  · intro hx
    refine ⟨fun b => spl.symm (x b, 0), (afsplit_mem_stdLat _ _).2 fun b => ?_, fun b => ?_⟩
    · refine (Formalism.L2.G.split_integral_completion F E v spl halg _).2 ?_
      rw [RingEquiv.apply_symm_apply]
      exact ⟨hx b, zero_mem _⟩
    · show (spl (spl.symm (x b, 0))).1 = x b
      rw [RingEquiv.apply_symm_apply]

theorem gco_chi_unit (H : Subgroup (GLG E n SG)) (lam : H →* ℂˣ) (x : levU hc n ST SG H) :
    ‖((levTyp lam x : ℂˣ) : ℂ)‖ = 1 := by
  have hfin : Finite (GLG E n SG) := inferInstance
  have hfo : IsOfFinOrder (levRed hc n ST SG H x) := isOfFinOrder_of_finite _
  obtain ⟨N, hN, hpow⟩ := hfo.exists_pow_eq_one
  have h1 : (levTyp lam x) ^ N = 1 := by
    show ((lam (levRed hc n ST SG H x))⁻¹) ^ N = 1
    rw [inv_pow, ← map_pow, hpow, map_one, inv_one]
  have h2 : ((levTyp lam x : ℂˣ) : ℂ) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 hN.ne'

end Core

end Formalism.L2.Col
end
end

