import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

section SlopeTestRemainingChoices

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem cwb_val_mem (l : List (lie (Jm ε))) : ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε := by
  intro X hX
  obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
  exact Y.2

theorem cwb_isKFin_Dw (h : Std ε σ) {v : H} (hv : IsKFin ε σ v) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    IsKFin ε σ (Dw σ l v) := by
  induction l with
  | nil => exact hv
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem X hY)
    exact isKFin_dRep n ε H σ h _ (ih hl') X (hl X (by simp))

theorem cwb_dRep_lin (h : Std ε σ) {w : H} (hw : Sm ε σ w) (a : ℝ) {X Y : Mx n} (hX : X ∈ lieSet ε)
    (hY : Y ∈ lieSet ε) : dRep σ (a • X + Y) w = (a : ℂ) • dRep σ X w + dRep σ Y w := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have hh : (Formalism.REAL.Jm ε).IsHermitian := GlobalTheory.SmVec.gram_herm (ε := ε) (P := 1) (by simp)
  have hd : (Formalism.REAL.Jm ε).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hG).ne_zero
  exact GlobalTheory.HolDict.LieAct.dRep_lin hh hd h.1 hw a hX hY

theorem cwb_Dw_sub (h : Std ε σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x)
    (hy : Sm ε σ y) : Dw σ l x - Dw σ l y = Dw σ l (x - y) := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have hxy : x - y ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ := Submodule.sub_mem _ hx hy
  have e := GlobalTheory.SmVec.word_add hG h.1 hl hy hxy
  have e' : Dw σ l x = GlobalTheory.SmVec.word σ l (y + (x - y)) := by rw [add_sub_cancel]; rfl
  rw [e', e]
  change GlobalTheory.SmVec.word σ l y + GlobalTheory.SmVec.word σ l (x - y) - GlobalTheory.SmVec.word σ l y = GlobalTheory.SmVec.word σ l (x - y)
  abel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ρ : Mx n → (E →L[ℂ] E)}

theorem cwb_mem_Fam (h : Std ε σ) {T₀ : H →ₗ[ℂ] E}
    (hd : ∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v →
      HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0)
    {v : H} (hv : IsKFin ε σ v) : (fun l : List (lie (Jm ε)) => T₀ (Dw σ (l.map Subtype.val) v)) ∈ Fam ε ρ := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have happ : ∀ (L₁ L₂ : List (Mx n)) (x : H), Dw σ (L₁ ++ L₂) x = Dw σ L₁ (Dw σ L₂ x) :=
    fun L₁ L₂ x => GlobalTheory.SmVec.word_append (π := σ) L₁ L₂ x
  have hcons : ∀ (Z : Mx n) (L : List (Mx n)) (x : H), Dw σ (Z :: L) x = dRep σ Z (Dw σ L x) :=
    fun _ _ _ => rfl
  have hK : ∀ l : List (lie (Jm ε)), IsKFin ε σ (Dw σ (l.map Subtype.val) v) :=
    fun l => cwb_isKFin_Dw h hv (cwb_val_mem l)
  have hS : ∀ l : List (lie (Jm ε)), Sm ε σ (Dw σ (l.map Subtype.val) v) :=
    fun l => h.2.2.1 _ (hK l)
  have hmem : ∀ X : lie (Jm ε), (X : Mx n) ∈ lieSet ε := fun X => cwb_val_mem [X] _ (by simp)
  unfold Fam
  refine ⟨?_, ?_, ?_⟩
  · intro l X
    exact hd X (hmem X) _ (hK l)
  · intro l₁ l₂ a X Y
    have hc : ((a • X + Y : lie (Jm ε)) : Mx n) = a • (X : Mx n) + (Y : Mx n) := rfl
    simp only [List.map_append, List.map_cons, happ, hcons, hc]
    have hw := hS l₂
    rw [cwb_dRep_lin h hw a (hmem X) (hmem Y)]
    have h1 : dRep σ (X : Mx n) (Dw σ (l₂.map Subtype.val) v) ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem X)
    have h2 : dRep σ (Y : Mx n) (Dw σ (l₂.map Subtype.val) v) ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem Y)
    have e1 := GlobalTheory.SmVec.word_add hG h.1 (cwb_val_mem l₁) (Submodule.smul_mem _ (a : ℂ) h1) h2
    have e2 := GlobalTheory.SmVec.word_smul hG h.1 (cwb_val_mem l₁) (a : ℂ) h1
    change T₀ (GlobalTheory.SmVec.word σ _ _) = _ • T₀ (GlobalTheory.SmVec.word σ _ _) + T₀ (GlobalTheory.SmVec.word σ _ _)
    rw [e1, e2, map_add, map_smul]
  · intro l₁ l₂ X Y Z hZ
    simp only [List.map_append, List.map_cons, happ, hcons]
    have hw := hS l₂
    have h1 : dRep σ (X : Mx n) (dRep σ (Y : Mx n) (Dw σ (l₂.map Subtype.val) v)) ∈
        GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 (GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem Y)) (hmem X)
    have h2 : dRep σ (Y : Mx n) (dRep σ (X : Mx n) (Dw σ (l₂.map Subtype.val) v)) ∈
        GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 (GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem X)) (hmem Y)
    rw [← map_sub, cwb_Dw_sub h (cwb_val_mem l₁) h1 h2,
      dRep_bracket n ε H σ h _ hw _ (hmem X) _ (hmem Y), ← hZ]

private theorem isKFin_add {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} {v w : H} (hv : IsKFin ε σ v) (hw : IsKFin ε σ w) :
    IsKFin ε σ (v + w) := by
  obtain ⟨S, hS, hvS, hSK⟩ := hv
  obtain ⟨S', hS', hwS, hSK'⟩ := hw
  refine ⟨S ⊔ S', ?_, Submodule.add_mem_sup hvS hwS, ?_⟩
  · haveI := hS
    haveI := hS'
    infer_instance
  · unfold IsKStableOn at hSK hSK' ⊢
    intro g hg x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hSK g hg y hy) (hSK' g hg z hz)

private theorem isKFin_smul {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} (c : ℂ) {v : H} (hv : IsKFin ε σ v) :
    IsKFin ε σ (c • v) := by
  obtain ⟨S, hS, hvS, hSK⟩ := hv
  exact ⟨S, hS, S.smul_mem c hvS, hSK⟩

private theorem isKFin_zero {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} : IsKFin ε σ (0 : H) := by
  refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
  unfold IsKStableOn
  intro g _ x hx
  rw [Submodule.mem_bot] at hx
  rw [hx, map_zero]
  exact Submodule.zero_mem _

private theorem mem_UJset_of_mem_Kset_iwasawa_decomposition {n : ℕ} {ε : Fin n → Bool} {k : Mx n} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have hu' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, show kᴴ * k = 1 from hu', Matrix.one_mul]

private theorem dw_apply_sigma_eq_sigma_dw_conj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {g : Mx n}
    (hg : g ∈ UJset ε) (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Dw σ l (σ g w) = σ g (Dw σ (l.map fun X => g⁻¹ * X * g) w) := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem X hY)
    have hX : X ∈ lieSet ε := hl X (by simp)
    change dRep σ X (Dw σ l (σ g w)) =
      σ g (dRep σ (g⁻¹ * X * g) (Dw σ (l.map fun X => g⁻¹ * X * g) w))
    rw [ih hl']
    have hs : Dw σ (l.map fun X => g⁻¹ * X * g) w ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ := by
      have hl'' : ∀ Y ∈ l.map (fun X => g⁻¹ * X * g), Y ∈ GlobalTheory.SmVec.lieG (Formalism.REAL.Jm ε) := by
        intro Y hY
        obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
        exact GlobalTheory.SmVec.conj_mem_lieG hG hg (hl' Z hZ)
      exact GlobalTheory.SmVec.word_mem hG h.1 hl'' hw
    exact GlobalTheory.SmVec.dRep_rep hG h.1 hs hg hX

end SlopeTestRemainingChoices

theorem casselmanWallach_banach : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → ∀ T₀ : H →ₗ[ℂ] E, (∀ k ∈ Kset ε, ∀ v, IsKFin ε σ v → T₀ (σ k v) = ρ k (T₀ v)) → (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0) → ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ (∀ g ∈ UJset ε, ∀ w, Sm ε σ w → T (σ g w) = ρ g (T w)) ∧ ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ ∀ w, Sm ε σ w → ‖T w‖ ≤ C * sobNorm σ S w := by
  intro hCW n ε H _ _ _ σ hσ E _ _ _ ρ hρ T₀ hK hd
  unfold GlobalTheory.Published.CasselmanWallach at hCW
  obtain ⟨hcl, p, π, dπ, hsm, hπ, hdπ, hp0⟩ := GlobalTheory.T.smooth_vectors_moderate_growth_smooth_frechet_rep n ε E ρ hρ
  haveI : IsUniformAddGroup (Fam ε ρ) := (Fam ε ρ).toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace (Fam ε ρ) := hcl.completeSpace_coe
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have happ : ∀ (L₁ L₂ : List (Mx n)) (x : H), Dw σ (L₁ ++ L₂) x = Dw σ L₁ (Dw σ L₂ x) :=
    fun L₁ L₂ x => GlobalTheory.SmVec.word_append (π := σ) L₁ L₂ x
  have hcons : ∀ (Z : Mx n) (L : List (Mx n)) (x : H), Dw σ (Z :: L) x = dRep σ Z (Dw σ L x) :=
    fun _ _ _ => rfl
  have hnil : ∀ x : H, Dw σ [] x = x := fun _ => rfl
  let KF : Submodule ℂ H :=
    { carrier := {v | IsKFin ε σ v}
      add_mem' := fun ha hb => isKFin_add ha hb
      zero_mem' := isKFin_zero
      smul_mem' := fun c _ hv => isKFin_smul c hv }
  let J : KF →ₗ[ℂ] Fam ε ρ :=
    { toFun := fun v => ⟨fun l => T₀ (Dw σ (l.map Subtype.val) v.1), cwb_mem_Fam hσ hd v.2⟩
      map_add' := fun v w => by
        apply Subtype.ext
        funext l
        have e := GlobalTheory.SmVec.word_add hG hσ.1 (cwb_val_mem l) (hσ.2.2.1 _ v.2) (hσ.2.2.1 _ w.2)
        show T₀ (Dw σ _ (v.1 + w.1)) = T₀ (Dw σ _ v.1) + T₀ (Dw σ _ w.1)
        rw [← map_add]
        exact congrArg T₀ e
      map_smul' := fun c v => by
        apply Subtype.ext
        funext l
        have e := GlobalTheory.SmVec.word_smul hG hσ.1 (cwb_val_mem l) c (hσ.2.2.1 _ v.2)
        show T₀ (Dw σ _ (c • v.1)) = c • T₀ (Dw σ _ v.1)
        rw [← map_smul]
        exact congrArg T₀ e }
  obtain ⟨T₁, hT₁⟩ := LinearMap.exists_extend J
  have hT₁v : ∀ (v : H) (hv : IsKFin ε σ v), T₁ v = J ⟨v, hv⟩ := fun v hv =>
    LinearMap.congr_fun hT₁ ⟨v, hv⟩
  have hJ : ∀ (v : H) (hv : IsKFin ε σ v) (l : List (lie (Jm ε))),
      (J ⟨v, hv⟩).1 l = T₀ (Dw σ (l.map Subtype.val) v) := fun _ _ _ => rfl
  have hGK : IsGKMap ε σ π dπ T₁ := by
    refine ⟨?_, ?_⟩
    · intro k hk v hv
      have hk' : k ∈ UJset ε := mem_UJset_of_mem_Kset_iwasawa_decomposition hk
      have hkv : IsKFin ε σ (σ k v) := by
        obtain ⟨S, hS, hvS, hSK⟩ := hv
        exact ⟨S, hS, hSK k hk v hvS, hSK⟩
      rw [hT₁v _ hkv, hT₁v _ hv]
      apply Subtype.ext
      funext l
      rw [hπ k hk' (J ⟨v, hv⟩) l, hJ, hJ, dw_apply_sigma_eq_sigma_dw_conj hσ hk' _ (cwb_val_mem l) (hσ.2.2.1 _ hv)]
      have hl : (l.map Subtype.val).map (fun X => k⁻¹ * X * k) = (l.map (adInv hk')).map Subtype.val := by
        simp only [List.map_map]
        rfl
      rw [hl, hK k hk _ (cwb_isKFin_Dw hσ hv (cwb_val_mem _))]
    · intro X hX v hv
      have hXv : IsKFin ε σ (dRep σ X v) := isKFin_dRep n ε H σ hσ v hv X hX
      rw [hT₁v _ hXv, hT₁v _ hv]
      apply Subtype.ext
      funext l
      rw [show (dπ X (J ⟨v, hv⟩)).1 l = (J ⟨v, hv⟩).1 (l ++ [⟨X, hX⟩]) from hdπ ⟨X, hX⟩ _ l, hJ, hJ]
      simp only [List.map_append, List.map_cons, List.map_nil, happ, hcons, hnil]
      try rfl
  obtain ⟨T', hT'0, hSG, -⟩ := hCW n ε H σ hσ.1 hσ.2.1 (Fam ε ρ) p π dπ hsm T₁ hGK
  unfold IsSmoothGMap at hSG
  obtain ⟨hTeq, hTbd⟩ := hSG
  refine ⟨(GlobalTheory.TypeSum.SmoothFrechet.ev ρ []).comp T', ?_, ?_, ?_⟩
  · intro v hv
    show (T' v).1 [] = T₀ v
    rw [hT'0 v hv, hT₁v v hv]
    rfl
  · intro g hg w hw
    show (T' (σ g w)).1 [] = ρ g ((T' w).1 [])
    rw [hTeq g hg w hw, hπ g hg (T' w) []]
    rfl
  · obtain ⟨S, C, hS, hSC⟩ := hTbd 0
    exact ⟨S, C, hS, fun w hw => (hp0 (T' w)).trans (hSC w hw)⟩

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInvOneSubConjMulTransposeAtZero
section
open scoped Matrix

namespace GlobalTheory.HermFrame

open Matrix Filter Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [DecidableEq m] [Fintype l]

theorem curv_inv_one_sub_mul {P : E → Matrix m l ℂ} {Q : E → Matrix l m ℂ} {z ξ η : E}
    {C : Matrix l m ℂ} (hP : ∀ x, MContDiffAt 2 P x) (hQ : ∀ x, MContDiffAt 2 Q x)
    (hP0 : P z = 0) (hdP : ∀ x, mdel P x ξ = 0) (hdQ : ∀ x, mdel Q x ξ = C) :
    curv (fun x => (1 - P x * Q x)⁻¹) z ξ η = -(mdbar P z η * C)ᵀ := by
  have hK : ∀ x, MContDiffAt 2 (fun x => 1 - P x * Q x) x :=
    fun x => (mContDiffAt_const 1).sub ((hP x).mul (hQ x))
  have hK0 : (1 - P z * Q z) = 1 := by rw [hP0]; simp
  have hd : ∀ x, mdel (fun x => 1 - P x * Q x) x ξ = -(P x * C) := fun x => by
    have h1 := (hP x).of_le one_le_two
    have h2 := (hQ x).of_le one_le_two
    simp only [sub_eq_add_neg]
    rw [mdel_add (mContDiffAt_const 1) (h1.mul h2).neg, mdel_neg, mdel_mul h1 h2, hdP, hdQ]
    simp
  have hdd : mddbar (fun x => 1 - P x * Q x) z ξ η = -(mdbar P z η * C) := by
    rw [← mdbar_mdel (hK z)]
    simp only [hd]
    rw [mdbar_neg, mdbar_mul ((hP z).of_le one_le_two) (mContDiffAt_const C)]
    simp
  have hu : IsUnit (1 - P z * Q z)ᵀ.det := by rw [hK0]; simp
  have e : (fun x => (1 - P x * Q x)⁻¹) = fun x => dualGram (1 - P x * Q x)ᵀ := by
    funext x; rw [dualGram, transpose_nonsing_inv, transpose_transpose]
  rw [e, curv_dual (hK z).transpose hu, curv_eq (hK z).transpose hu,
    mdel_transpose (fun x => 1 - P x * Q x), hd,
    show mddbar (fun x => (1 - P x * Q x)ᵀ) z ξ η = (mddbar (fun x => 1 - P x * Q x) z ξ η)ᵀ from rfl,
    hdd, hK0, hP0]
  simp

end

section

variable {n : ℕ} {a b : Type*}

theorem mContDiffAt_coordMatrix (f : a → b → Fin n) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w := fun i j =>
  ((EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ).contDiff.contDiffAt

theorem mdel_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ =
      Matrix.of fun i j => ξ (f i j) := by
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ := EuclideanSpace.proj (𝕜 := ℂ) (f i j)
  change del L w ξ = L ξ
  rw [del_eq_fderiv L.differentiableAt, L.fderiv]

theorem mdbar_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ = 0 := by
  have h := mdel_add_mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ
  rw [mdel_coordMatrix] at h
  rw [← add_right_inj (Matrix.of fun i j => ξ (f i j)), h, add_zero]
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ
  change fderiv ℝ L w ξ = L ξ
  rw [L.fderiv]

end

theorem curv_inv_one_sub_conj_mul_transpose_zero : ∀ {n r s : ℕ} (f g : Fin r → Fin s → Fin n) (ξ η : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.HermFrame.curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 ξ η = -((Matrix.of fun i j => ξ (g i j)) * (Matrix.of fun i j => η (f i j))ᴴ) := by
  intro n r s f g ξ η
  let Z : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (f i j)
  let W : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (g i j)
  have h := curv_inv_one_sub_mul (P := fun u => (Z u)ᴴᵀ) (Q := fun u => (W u)ᵀ) (z := 0) (ξ := ξ)
    (η := η) (C := (W ξ)ᵀ) (fun x => (mContDiffAt_coordMatrix f x).conjTranspose.transpose)
    (fun x => (mContDiffAt_coordMatrix g x).transpose) (by ext i j; simp [Z])
    (fun x => by
      rw [mdel_transpose (fun u => (Z u)ᴴ), mdel_conjTranspose, mdbar_coordMatrix]; simp)
    (fun x => by rw [mdel_transpose W, mdel_coordMatrix])
  rw [mdbar_transpose (fun u => (Z u)ᴴ), mdbar_conjTranspose, mdel_coordMatrix, ← transpose_mul,
    transpose_transpose] at h
  exact h

end GlobalTheory.HermFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpen
section
open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory

theorem iSup_measure_apply_eq_zero {α κ : Type*} [MeasurableSpace α] (μ : κ → Measure α) {S : Set α}
    (hS : MeasurableSet S) (h : ∀ i, μ i S = 0) : (⨆ i, μ i) S = 0 := by
  have hle : (⨆ i, μ i) ≤ (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => ?_
    calc μ i = (μ i).restrict Sᶜ :=
          (Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 (h i))).symm
      _ ≤ (⨆ i, μ i).restrict Sᶜ := Measure.restrict_mono subset_rfl (le_iSup μ i)
  refine le_antisymm ?_ (zero_le)
  calc (⨆ i, μ i) S ≤ (⨆ i, μ i).restrict Sᶜ S := Measure.le_iff'.1 hle S
    _ = 0 := by rw [Measure.restrict_apply hS, Set.inter_compl_self, measure_empty]

theorem chernTopPart_neg_eq_zero_of_nonneg {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R : MvPolynomial (ι × ℕ) ℝ)
    (h : ∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) :
    chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  have hS : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  unfold chernTopPart glueMeas
  refine iSup_measure_apply_eq_zero _ hS fun c => ?_
  rw [chartMeas_apply c.e _ hS]
  have hm : MeasurableSet (c.e '' (c.e.source ∩ ptsIn X.str σ O)) :=
    measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) Set.inter_subset_left
  rw [setLIntegral_congr_fun hm (g := fun _ => 0) ?_, MeasureTheory.lintegral_zero]
  rintro _ ⟨y, ⟨hys, hyS⟩, rfl⟩
  have hz : c.e.symm (c.e y) ∈ c.e.source ∩ ptsIn X.str σ O := by
    rw [c.e.left_inv hys]; exact ⟨hys, hyS⟩
  beta_reduce
  generalize c.e.symm (c.e y) = z at hz ⊢
  apply ENNReal.ofReal_eq_zero.2
  have := h z hz.2 c hz.1 _ (E.nonempty (under z)).choose_spec
  push_cast
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReLev0
section
noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}

abbrev recOf (Z : Later B C) : D7 := assemble B C Z.W Z.V Z.S Z.N Z.G

variable {Z : Later B C} (Z' : Later B C)

set_option maxHeartbeats 4000000 in

def atTTRe {u : B.Word} (A : AtTTied (D := recOf Z) u) : AtTTied (D := recOf Z') u := { A with }

set_option maxHeartbeats 4000000 in

def clsRe {u : B.Word} {i : ℕ} {hi : i ≤ B.R.m} (K : ClsTied (D := recOf Z) u i hi) : ClsTied (D := recOf Z') u i hi := { K with }

set_option maxHeartbeats 4000000 in

def valRe {u : B.Word} {eV : (C.mem u).A.vT ≃ PlT (recOf Z) u} {i : ℕ} {hi : i ≤ B.R.m} {K : ClsTied (D := recOf Z) u i hi}
    (W : ValTied (D := recOf Z) u eV i hi K) : ValTied (D := recOf Z') u eV i hi (clsRe Z' K) := { W with }

set_option maxHeartbeats 4000000 in

def lvRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {i : ℕ} {hi : i ≤ B.R.m} (P : LvTied (D := recOf Z) u A i hi) :
    LvTied (D := recOf Z') u (atTTRe Z' A) i hi := { P with }

set_option maxHeartbeats 4000000 in

def clsPRe {u : B.Word} (K : ClsPTied (D := recOf Z) u) : ClsPTied (D := recOf Z') u := { K with }

set_option maxHeartbeats 4000000 in

def valPRe {u : B.Word} {K : ClsPTied (D := recOf Z) u} (W : ValPTied (D := recOf Z) u K) :
    ValPTied (D := recOf Z') u (clsPRe Z' K) := { W with }

set_option maxHeartbeats 4000000 in

def tilRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {K : ClsPTied (D := recOf Z) u} {P : LvTied (D := recOf Z) u A B.R.m le_rfl}
    (Tl : TilTied (D := recOf Z) u A K P) : TilTied (D := recOf Z') u (atTTRe Z' A) (clsPRe Z' K) (lvRe Z' P) := { Tl with }

set_option maxHeartbeats 4000000 in

def tilAdRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {K : ClsPTied (D := recOf Z) u} {P : LvTied (D := recOf Z) u A B.R.m le_rfl}
    {Tl : TilTied (D := recOf Z) u A K P} {Km : ClsTied (D := recOf Z) u B.R.m le_rfl} (Ta : TilAd (D := recOf Z) Tl Km) :
    TilAd (D := recOf Z') (tilRe Z' Tl) (clsRe Z' Km) := { Ta with }

set_option maxHeartbeats 4000000 in

def chartRe {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {i : ℕ} {hi : i ≤ B.R.m} {cl : Type}
    {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    (K : LevelChart (recOf Z) T bad i hi stab lat) : LevelChart (recOf Z') T bad i hi stab lat := { K with }

set_option maxHeartbeats 4000000 in

def lvGRe {u : B.Word} {T : ℕ} {res : ∀ v : (C.mem u).A.vT, 𝓞 B.host.E →+* (C.mem u).A.Fv v} {i : ℕ} {hi : i ≤ B.R.m}
    {lat : (C.mem u).C.cls i → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    (L : LevelCompatibleLattices (D := recOf Z) (u := u) (C.fm u) T res i hi lat) : LevelCompatibleLattices (D := recOf Z') (u := u) (C.fm u) T res i hi lat := { L with }

set_option maxHeartbeats 16000000 in

def formsRe {u : B.Word} {Ch : ℕ → Type} {chOf : ∀ i, (C.mem u).C.cls i → Ch i} (T : FormsTiedSym (recOf Z) u Ch chOf) :
    FormsTiedSym (recOf Z') u Ch chOf :=
  { T with
    atT := atTTRe Z' T.atT
    cls := fun i hi h => clsRe Z' (T.cls i hi h)
    val := fun i hi h => valRe Z' (T.val i hi h)
    lv := fun i hi => lvRe Z' (T.lv i hi)
    ch := fun i h1 h2 β => chartRe Z' (T.ch i h1 h2 β)
    valC := fun i h1 h2 => { T.valC i h1 h2 with }
    dilC := fun i h1 h2 => { T.dilC i h1 h2 with }
    lvC := fun i h1 h2 => lvGRe Z' (T.lvC i h1 h2)
    clsP := clsPRe Z' T.clsP
    valP := valPRe Z' T.valP
    til := tilRe Z' T.til
    tilAd := tilAdRe Z' T.tilAd }

set_option maxHeartbeats 4000000 in

def hermChRe (H : Formalism.L2.Herm.HermColsCh (recOf Z)) : Formalism.L2.Herm.HermColsCh (recOf Z') := { H with }

set_option maxHeartbeats 4000000 in

def atTRe {u : B.Word}
    {e : (C.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 B.host.F) // (((C.mem u).A.T : ℕ) : 𝓞 B.host.F) ∈ v.asIdeal}}
    {eF : ∀ v : (C.mem u).A.vT, (C.mem u).A.Fv v ≃+* (𝓞 B.host.F ⧸ (e v).1.asIdeal)} (A : Formalism.L2.Herm.AtT (recOf Z) u e eF) :
    Formalism.L2.Herm.AtT (recOf Z') u e eF := { A with }

set_option maxHeartbeats 4000000 in

def hermRe (H : Formalism.L2.Herm.ColsHermS (recOf Z)) : Formalism.L2.Herm.ColsHermS (recOf Z') :=
  { H with
    base := hermChRe Z' H.base
    atT := fun u => atTRe Z' (H.atT u)
    ad := { H.ad with } }

set_option maxHeartbeats 16000000 in

def colsRe (T : ColsTiedSym (recOf Z)) : ColsTiedSym (recOf Z') :=
  { T with
    herm := hermRe Z' T.herm
    forms := fun u => formsRe Z' (T.forms u)
    gl_const := T.gl_const }

end GlobalTheory.Mem.Top.ColOwe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteUnitaryArchimedeanPointsDistinctPlacesStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ τ' : E →+* ℂ), InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ x ∈ embU n τ, ∀ y ∈ embU n τ', Commute x y := by
  first | exact @GlobalTheory.UnitaryBC.embU_commute | exact GlobalTheory.UnitaryBC.embU_commute | (intros; apply GlobalTheory.UnitaryBC.embU_commute <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommutingEndAlgebrasCommonFixedVectorStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_fixed_by_commuting_rankOne_images : ∀ (ι : Type) [Fintype ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] [∀ v, FiniteDimensional ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v) (ℓ : ∀ v, Module.Dual ℂ (Wv v)), Nontrivial V → (∀ v, ℓ v (w v) = 1) → (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) → ∃ y : V, y ≠ 0 ∧ ∀ v, Φ v ((ℓ v).smulRight (w v)) y = y := by
  first | exact @GlobalTheory.commuting_endAlgebras_common_fixed_vector | exact GlobalTheory.commuting_endAlgebras_common_fixed_vector | (intros; apply GlobalTheory.commuting_endAlgebras_common_fixed_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameFamilyLongerFlagGenericLineStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι] (m k k' : ι → ℕ) (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω'), k' τ = k τ + 1 → (∀ τ', τ' ≠ τ → k' τ' = k τ') → A₀ ∈ S.S (genericPoint M.Z) → (∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A))) → ProjPoints M EE M' φ f s → ∃ S' : Fr M' m k', ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z' := by
  first | exact @GlobalTheory.FlagBundle.exists_fr_stepSet | exact GlobalTheory.FlagBundle.exists_fr_stepSet | (intros; apply GlobalTheory.FlagBundle.exists_fr_stepSet <;> assumption)
end

