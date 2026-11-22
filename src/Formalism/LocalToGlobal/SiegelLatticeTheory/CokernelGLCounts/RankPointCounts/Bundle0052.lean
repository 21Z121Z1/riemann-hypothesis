import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0049

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfB
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.LprU

open Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem dl_full {r : ℕ} (f f' : Fin (r + 1) → V) : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dif_pos le_rfl]
  simp [Fin.castLE_rfl]

def Iso' {r : ℕ} (H : HermSp M V) (f' : Fin (r + 1) → V) : Prop :=
  ∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f' a) (f' b) = 0

theorem mem_perp_X {r : ℕ} (f' : Fin (r + 1) → V) {x : V} (hx : ∀ i : Fin r, H.h x (f' i.castSucc) = 0) :
    x ∈ H.perp (H.X f') := fun y hy => h_right_zero hx hy

theorem X_le_perp {r : ℕ} {f' : Fin (r + 1) → V} (hK : Iso' H f') : H.X f' ≤ H.perp (H.X f') := by
  unfold HermSp.X
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact mem_perp_X f' (fun i => hK _ _ (Or.inl (Fin.castSucc_lt_last a).ne))

theorem z_mem_perp {r : ℕ} {f' : Fin (r + 1) → V} (hK : Iso' H f') : f' (Fin.last r) ∈ H.perp (H.X f') := mem_perp_X f' (fun i => hK _ _ (Or.inr (Fin.castSucc_lt_last i).ne))

theorem om_mem_perp {r : ℕ} (f f' : Fin (r + 1) → V) : H.om f f' ∈ H.perp (H.X f') := by
  apply mem_perp_X
  intro i
  unfold HermSp.om
  rw [Formalism.L2.SG.CntLocal.h_sum_left]
  have e : ∀ a, H.h (M.L.cj ((H.Zhat f f').adjugate (Fin.last r) a) • f a) (f' i.castSucc) =
      M.L.cj ((H.Zhat f f').adjugate (Fin.last r) a * (H.Zhat f f') a i.castSucc) := by
    intro a
    rw [H.h_smul_left, H.h_herm (f' i.castSucc) (f a), map_mul]
    rfl
  simp only [e]
  rw [← map_sum]
  have h2 : ∑ a, (H.Zhat f f').adjugate (Fin.last r) a * (H.Zhat f f') a i.castSucc =
      ((H.Zhat f f').adjugate * H.Zhat f f') (Fin.last r) i.castSucc := (Matrix.mul_apply ..).symm
  rw [h2, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne',
    smul_zero, map_zero]

theorem w_zero_le_perp_first {r : ℕ} (f f' : Fin (r + 1) → V) : H.W0 f f' ≤ H.perp (H.X f) := by
  intro v hv x hx
  exact hv x (Submodule.mem_sup_left (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, rfl⟩) hx))

theorem w_zero_le_perp_second {r : ℕ} (f f' : Fin (r + 1) → V) : H.W0 f f' ≤ H.perp (H.X f') := by
  intro v hv x hx
  exact hv x (Submodule.mem_sup_right (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, rfl⟩) hx))

theorem Xp_le_span {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Xp f ⊔ H.Xp f' ≤ Submodule.span E (Set.range (Sum.elim f f')) := by
  apply sup_le
  · apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨Sum.inl a, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨Sum.inr a, rfl⟩

theorem X_le_span {r : ℕ} (f f' : Fin (r + 1) → V) : H.X f ≤ Submodule.span E (Set.range (Sum.elim f f')) := by
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact ⟨Sum.inl a.castSucc, rfl⟩

theorem decomp_perp {r : ℕ} (t : Term V M r) (hN : GramInvE H (Sum.elim t.f t.f'))
    (hD : IsUnit (H.Zhat t.f t.f').det) (hK : Iso' H t.f') {x : V} (hx : x ∈ H.perp (H.X t.f')) :
    ∃ (w : V) (μ c : E) (xX : V), w ∈ H.W0 t.f t.f' ∧ xX ∈ H.X t.f' ∧
      x = w + μ • H.om t.f t.f' + xX + c • t.f' (Fin.last r) := by
  obtain ⟨c, hc⟩ := decompE hN x
  set w := x - ∑ k, c k • Sum.elim t.f t.f' k with hwdef
  have hwW : w ∈ H.W0 t.f t.f' := fun y hy => h_right_zero hc (Xp_le_span t.f t.f' hy)
  set y : V := ∑ a, c (Sum.inl a) • t.f a with hy
  set xX : V := ∑ i : Fin r, c (Sum.inr i.castSucc) • t.f' i.castSucc with hxX
  have hxXm : xX ∈ H.X t.f' :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsplit : ∑ k, c k • Sum.elim t.f t.f' k = y + xX + c (Sum.inr (Fin.last r)) • t.f' (Fin.last r) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Fin.sum_univ_castSucc (fun b => c (Sum.inr b) • t.f' b)]
    abel
  have hx' : x = w + y + xX + c (Sum.inr (Fin.last r)) • t.f' (Fin.last r) := by
    rw [hwdef, hsplit]; abel
  have hyo : ∀ b, b ≠ Fin.last r → H.h y (t.f' b) = 0 := by
    intro b hb
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hb
    have hyv : y = x - w - xX - c (Sum.inr (Fin.last r)) • t.f' (Fin.last r) := by rw [hx']; abel
    have e1 : H.h x (t.f' i.castSucc) = 0 := hx _ (Submodule.subset_span ⟨i, rfl⟩)
    have e2 : H.h w (t.f' i.castSucc) = 0 := hc (Sum.inr i.castSucc)
    have e3 : H.h xX (t.f' i.castSucc) = 0 := X_le_perp hK hxXm _ (Submodule.subset_span ⟨i, rfl⟩)
    have e4 : H.h (t.f' (Fin.last r)) (t.f' i.castSucc) = 0 := hK _ _ (Or.inr (Fin.castSucc_ne_last i))
    rw [hyv, ← hL_apply]
    simp only [map_sub, map_smul, hL_apply, e1, e2, e3, e4, smul_zero, sub_zero]
  have hyom := y_eq_om t.f t.f' (fun a => c (Sum.inl a)) hyo
  have hu : IsUnit (M.L.cj (H.Zhat t.f t.f').det) := hD.map M.L.cj
  refine ⟨w, ((hu.unit⁻¹ : Eˣ) : E) * H.h y (t.f' (Fin.last r)), c (Sum.inr (Fin.last r)), xX, hwW, hxXm, ?_⟩
  have hy2 : y = (((hu.unit⁻¹ : Eˣ) : E) * H.h y (t.f' (Fin.last r))) • H.om t.f t.f' := by
    rw [mul_smul, ← hyom, smul_smul, hu.val_inv_mul, one_smul]
  rw [hx', ← hy2]

theorem psi_unique {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (ψ ψ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (hN1 : GramInvE H (Sum.elim t₁.f t₁.f')) (hN2 : GramInvE H (Sum.elim t₂.f t₂.f'))
    (hD1 : IsUnit (H.Zhat t₁.f t₁.f').det) (hD2 : IsUnit (H.Zhat t₂.f t₂.f').det)
    (hK1 : Iso' H t₁.f') (hK2 : Iso' H t₂.f')
    (hI : H.Ident t₁ t₂ φ ψ) (hI' : H.Ident t₁ t₂ φ ψ')
    (hz : H.SendsTo ψ.toLinearMap 1 1 (t₁.f' (Fin.last r)) (t₂.f' (Fin.last r)))
    (hz' : H.SendsTo ψ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (t₂.f' (Fin.last r))) : ψ = ψ' := by

  have gW : ∀ (w : V) (hw : w ∈ H.W0 t₁.f t₁.f'),
      ψ (H.mkW t₁.f' ⟨w, w_zero_le_perp_second _ _ hw⟩) = ψ' (H.mkW t₁.f' ⟨w, w_zero_le_perp_second _ _ hw⟩) := by
    intro w hw
    obtain ⟨w₂, hw₂, hφ1, hψ1⟩ := hI.2.2.1 w hw
    obtain ⟨w₂', hw₂', hφ2, hψ2⟩ := hI'.2.2.1 w hw
    have e1 := hφ1 ⟨w, w_zero_le_perp_first _ _ hw⟩ ⟨w₂, w_zero_le_perp_first _ _ hw₂⟩ rfl rfl
    have e2 := hφ2 ⟨w, w_zero_le_perp_first _ _ hw⟩ ⟨w₂', w_zero_le_perp_first _ _ hw₂'⟩ rfl rfl
    rw [one_smul, one_smul] at e1 e2
    have e12 : H.mkW t₂.f ⟨w₂, w_zero_le_perp_first _ _ hw₂⟩ = H.mkW t₂.f ⟨w₂', w_zero_le_perp_first _ _ hw₂'⟩ := by
      rw [← e1, ← e2]
    have hsub : w₂ - w₂' ∈ H.X t₂.f := by
      have h := (Submodule.Quotient.eq _).1 e12
      simpa using h
    have hz0 : w₂ - w₂' = 0 := by
      refine eqz hN2 (X_le_span _ _ hsub) fun k => ?_
      have hk : Sum.elim t₂.f t₂.f' k ∈ H.Xp t₂.f ⊔ H.Xp t₂.f' := by
        cases k with
        | inl a => exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
        | inr b => exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, rfl⟩)
      exact (H.W0 t₂.f t₂.f').sub_mem hw₂ hw₂' _ hk
    have hww : w₂ = w₂' := sub_eq_zero.1 hz0
    have f1 := hψ1 ⟨w, w_zero_le_perp_second _ _ hw⟩ ⟨w₂, w_zero_le_perp_second _ _ hw₂⟩ rfl rfl
    have f2 := hψ2 ⟨w, w_zero_le_perp_second _ _ hw⟩ ⟨w₂', w_zero_le_perp_second _ _ hw₂'⟩ rfl rfl
    rw [one_smul, one_smul] at f1 f2
    subst hww
    exact f1.trans f2.symm

  have gom : ψ (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) = ψ' (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := by
    have e1 := hI.2.2.2.2.1 ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩ ⟨H.om t₂.f t₂.f', om_mem_perp _ _⟩ rfl rfl
    have e2 := hI'.2.2.2.2.1 ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩ ⟨H.om t₂.f t₂.f', om_mem_perp _ _⟩ rfl rfl
    have hu : IsUnit (M.L.cj (H.Dl t₂.f t₂.f' (r + 1))) := by rw [dl_full]; exact hD2.map M.L.cj
    have e3 : M.L.cj (H.Dl t₂.f t₂.f' (r + 1)) • ψ (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) =
        M.L.cj (H.Dl t₂.f t₂.f' (r + 1)) • ψ' (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := by
      have a1 : ψ.toLinearMap (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) =
          ψ (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := rfl
      have a2 : ψ'.toLinearMap (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) =
          ψ' (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := rfl
      rw [← a1, ← a2, e1, e2]
    have e4 := congrArg (fun q => ((hu.unit⁻¹ : Eˣ) : E) • q) e3
    simp only [smul_smul] at e4
    rwa [hu.val_inv_mul, one_smul, one_smul] at e4

  have gz : ψ (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩) =
      ψ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩) := by
    have e1 := hz ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩ ⟨t₂.f' (Fin.last r), z_mem_perp hK2⟩ rfl rfl
    have e2 := hz' ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩ ⟨t₂.f' (Fin.last r), z_mem_perp hK2⟩ rfl rfl
    rw [one_smul, one_smul] at e1 e2
    exact e1.trans e2.symm
  apply LinearEquiv.ext
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨w, μ, c, xX, hw, hxX, hdec⟩ := decomp_perp t₁ hN1 hD1 hK1 hx
  have hq : (⟨x, hx⟩ : H.perp (H.X t₁.f')) = ⟨w, w_zero_le_perp_second _ _ hw⟩ + μ • ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩ +
      ⟨xX, X_le_perp hK1 hxX⟩ + c • ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩ := Subtype.ext hdec
  have h0 : H.mkW t₁.f' ⟨xX, X_le_perp hK1 hxX⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hxX
  show ψ (H.mkW t₁.f' ⟨x, hx⟩) = ψ' (H.mkW t₁.f' ⟨x, hx⟩)
  rw [hq, map_add, map_add, map_add, map_smul, map_smul, h0, add_zero]
  simp only [map_add, map_smul]
  rw [gW w hw, gom, gz]

end Formalism.MainNotions.S.Loc.HermSp.LprU
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FibSumOf
section
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem fibSum_of (hD : TupFun M δ u u' F0 what₂) (hC : RepAtTup M δ u u' F0 what₂) (hB : OrbZT M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.FCount.FibSum M δ u u' F0 what₂ := by
  intro hA hT hP hN hR hE w hG Z hZ hfin
  have hpre : Pre M δ u u' F0 what₂ := ⟨hA, hT, hP, hN, hR, hE⟩
  let S : Set (TermDef.Term D u u' F0 what₂) := {γ | EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z}
  have hrep : ∀ γ ∈ S, RepIn u u' F0 what₂ γ Z := fun γ hγ => hC hpre γ w hG Z hZ hγ.1 hγ.2
  have hclsFin : ∀ Λ ∈ what₂, (clsSet F0 u' Λ Z).Finite := fun Λ hΛ =>
    Set.encard_ne_top_iff.1 (by rw [← cntE_eq]; exact hfin Λ hΛ)
  have hsub : ∀ γ : TermDef.Term D u u' F0 what₂,
      PairVal.orbT D u u' F0 what₂ γ Z ⊆ clsSet F0 u' γ.lam Z := by
    rintro γ O ⟨F', hF', -, rfl⟩
    exact ⟨F', hF', rfl⟩
  have horbFin : ∀ γ : TermDef.Term D u u' F0 what₂, (PairVal.orbT D u u' F0 what₂ γ Z).Finite := fun γ =>
    (hclsFin γ.lam γ.mem).subset (hsub γ)
  have hne : ∀ γ ∈ S, (PairVal.orbT D u u' F0 what₂ γ Z).Nonempty := by
    intro γ hγ
    obtain ⟨F', hF', hr⟩ := hrep γ hγ
    exact ⟨_, F', hF', hr, rfl⟩
  have hnc : ∀ γ ∈ S, (PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard = (PairVal.orbT D u u' F0 what₂ γ Z).ncard := by
    intro γ hγ
    rw [Set.ncard_def, Set.ncard_def, hB hpre γ w Z hγ.1 hZ (hrep γ hγ)]

  have hSfin : S.Finite := by
    have hU : S ⊆ ⋃ Λ ∈ (what₂ : Set (Submodule (𝓞 D.host.E) (VS D).V)), ⋃ O ∈ clsSet F0 u' Λ Z,
        {γ : TermDef.Term D u u' F0 what₂ | γ.lam = Λ ∧ O ∈ PairVal.orbT D u u' F0 what₂ γ Z} := by
      intro γ hγ
      obtain ⟨O, hO⟩ := hne γ hγ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨γ.lam, γ.mem, O, hsub γ hO, rfl, hO⟩
    refine Set.Finite.subset ?_ hU
    refine Set.Finite.biUnion what₂.finite_toSet (fun Λ hΛ => Set.Finite.biUnion (hclsFin Λ hΛ) (fun O _ => ?_))
    refine Set.Subsingleton.finite (fun γ₁ h₁ γ₂ h₂ => ?_)
    exact orbT_disj (h₁.1.trans h₂.1.symm) h₁.2 h₂.2

  have hrow : ∀ Λ ∈ what₂, ∑ γ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
      ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) = ((clsSet F0 u' Λ Z).ncard : ℝ) := by
    intro Λ hΛ
    have hbU : (hclsFin Λ hΛ).toFinset =
        (hSfin.toFinset.filter (fun γ => γ.lam = Λ)).biUnion (fun γ => (horbFin γ).toFinset) := by
      ext O
      simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨F', hF', rfl⟩
        refine ⟨termOf Λ hΛ F' (pd_of_ez hF'), ⟨⟨eligAt_termOf Λ hΛ hZ hF', ?_⟩, rfl⟩,
          mem_orbT_termOf Λ hΛ hF'⟩
        exact hD hpre _ w Z (eligAt_termOf Λ hΛ hZ hF') hZ (repIn_termOf Λ hΛ hF')
      · rintro ⟨γ, ⟨-, hγΛ⟩, hO⟩
        have := hsub γ hO
        rw [hγΛ] at this
        exact this
    have hdisj : ∀ γ₁ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ), ∀ γ₂ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
        γ₁ ≠ γ₂ → Disjoint (horbFin γ₁).toFinset (horbFin γ₂).toFinset := by
      intro γ₁ h₁ γ₂ h₂ hne12
      rw [Finset.disjoint_left]
      intro O hO₁ hO₂
      rw [Set.Finite.mem_toFinset] at hO₁ hO₂
      exact hne12 (orbT_disj ((Finset.mem_filter.1 h₁).2.trans (Finset.mem_filter.1 h₂).2.symm) hO₁ hO₂)
    rw [Set.ncard_eq_toFinset_card _ (hclsFin Λ hΛ), hbU, Finset.card_biUnion hdisj]
    push_cast
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Set.ncard_eq_toFinset_card _ (horbFin γ)]

  have hreal : ∑ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) =
      CntLocal.nu (CntLocal.Tn u') F0 what₂ Z := by
    have e1 : ∀ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) =
        PairVal.massRow D F0 what₂ γ.lam * ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) := by
      intro γ hγ
      rw [hnc γ ((Set.Finite.mem_toFinset hSfin).1 hγ)]
      rfl
    rw [Finset.sum_congr rfl e1]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun γ : TermDef.Term D u u' F0 what₂ => γ.lam) (t := what₂)
      (fun γ _ => γ.mem)]
    have e2 : ∀ Λ ∈ what₂, ∑ γ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
        PairVal.massRow D F0 what₂ γ.lam * ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) =
        PairVal.massRow D F0 what₂ Λ * ((clsSet F0 u' Λ Z).ncard : ℝ) := by
      intro Λ hΛ
      rw [← hrow Λ hΛ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun γ hγ => ?_)
      rw [(Finset.mem_filter.1 hγ).2]
    rw [Finset.sum_congr rfl e2]
    unfold CntLocal.nu PairVal.massRow
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun Λ _ => ?_)
    rw [Set.ncard_def, ← cntE_eq]
    unfold Formalism.MainNotions.S.Cnt.massRows
    ring
  haveI : Fintype {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} := hSfin.fintype
  have hs := hasSum_fintype (fun γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} =>
    (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
  have h1 : ∑ γ ∈ hSfin.toFinset, (PairVal.massTerm γ : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) =
      ∑ γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z},
        (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ) :=
    Finset.sum_subtype hSfin.toFinset (fun γ => Set.Finite.mem_toFinset hSfin) _
  have h2 : ((∑ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) : ℝ) : ℂ) =
      ∑ γ ∈ hSfin.toFinset, (PairVal.massTerm γ : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) := by
    push_cast
    rfl
  have key := h1.symm.trans (h2.symm.trans (congrArg (fun x : ℝ => (x : ℂ)) hreal))
  exact Eq.mpr (congrArg (HasSum _) key.symm) hs

end Count

end Formalism.L2.SG.Pf.FibPart
end
end

