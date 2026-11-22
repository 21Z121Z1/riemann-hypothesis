import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LeadMinorEMulUpper

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LocPBLatTransport
section
noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

abbrev fO (n : S.V ≃ₗ[E] S.V) : S.V →ₗ[𝓞 E] S.V := (n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)

theorem fO_apply (n : S.V ≃ₗ[E] S.V) (v : S.V) : fO n v = n v := rfl

theorem gmap_eq_map (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n M = M.map (fO n) := rfl

theorem mem_gmap_iff (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) (v : S.V) :
    v ∈ Formalism.HermitianLatticesTheory.gmap n M ↔ n.symm v ∈ M := by
  rw [gmap_eq_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [fO_apply] using hw
  · intro hv
    exact ⟨n.symm v, hv, by simp [fO_apply]⟩

theorem mem_localization_iff (P : Ideal (𝓞 E)) [P.IsPrime] (M : Submodule (𝓞 E) S.V) (v : S.V) :
    v ∈ Formalism.HermitianLatticesTheory.localization₂ P M ↔ ∃ s ∈ P.primeCompl, s • v ∈ M := Iff.rfl

theorem locP_gmap (P : Ideal (𝓞 E)) [P.IsPrime] (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.localization₂ P (Formalism.HermitianLatticesTheory.gmap n M) = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.localization₂ P M) := by
  ext v
  rw [mem_localization_iff, mem_gmap_iff, mem_localization_iff]
  constructor
  · rintro ⟨s, hs, hsv⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff] at hsv
    have e : n.symm (s • v) = s • n.symm v := (fO n.symm).map_smul s v
    rwa [e] at hsv
  · rintro ⟨s, hs, hsv⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff]
    have e : n.symm (s • v) = s • n.symm v := (fO n.symm).map_smul s v
    rwa [e]

theorem gmap_injective (n : S.V ≃ₗ[E] S.V) {A B : Submodule (𝓞 E) S.V}
    (h : Formalism.HermitianLatticesTheory.gmap n A = Formalism.HermitianLatticesTheory.gmap n B) : A = B := by
  ext v
  have := SetLike.ext_iff.1 h (n v)
  simpa [mem_gmap_iff] using this

theorem sup_span_swap {M : Submodule (𝓞 E) S.V} {a b : S.V} (h : a - b ∈ M) :
    M ⊔ Submodule.span (𝓞 E) {a} = M ⊔ Submodule.span (𝓞 E) {b} := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have e : a = (a - b) + b := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b))
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have e : b = a - (a - b) := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a))
      (Submodule.mem_sup_left h)

theorem gmap_span_singleton (n : S.V ≃ₗ[E] S.V) (v : S.V) :
    Formalism.HermitianLatticesTheory.gmap n (Submodule.span (𝓞 E) {v}) = Submodule.span (𝓞 E) {n v} := by
  rw [gmap_eq_map, Submodule.map_span, Set.image_singleton, fO_apply]

theorem gmap_sup (n : S.V ≃ₗ[E] S.V) (A B : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap n A ⊔ Formalism.HermitianLatticesTheory.gmap n B := by
  rw [gmap_eq_map, gmap_eq_map, gmap_eq_map, Submodule.map_sup]

variable {Λ : Submodule (𝓞 E) S.V}

theorem autLam_maps {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {v : S.V} (hv : v ∈ Λ) : n v ∈ Λ := by
  have h : n v ∈ Formalism.HermitianLatticesTheory.gmap n Λ := (mem_gmap_iff n Λ (n v)).2 (by simpa using hv)
  rwa [hn.2] at h

theorem autLam_symm_maps {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {v : S.V} (hv : v ∈ Λ) :
    n.symm v ∈ Λ := by
  rw [← hn.2] at hv
  exact (mem_gmap_iff n Λ v).1 hv

theorem mem_XLam {F : LFlag S r T} {v : S.V} : v ∈ XLam Λ F ↔ v ∈ Λ ∧ v ∈ Xsp F := by
  unfold XLam
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem]

theorem gmap_XLam_self {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    Formalism.HermitianLatticesTheory.gmap n (XLam Λ F) = XLam Λ F := by
  have hni : n.symm ∈ NLam Λ F := nlam_inv hn
  ext v
  rw [mem_gmap_iff, mem_XLam, mem_XLam]
  constructor
  · rintro ⟨h1, h2⟩
    have a1 := autLam_maps hn.1 h1
    have a2 := nlam_maps_X hn _ h2
    simp only [LinearEquiv.apply_symm_apply] at a1 a2
    exact ⟨a1, a2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨autLam_symm_maps hn.1 h1, nlam_maps_X hni _ h2⟩

theorem nlam_z_sub {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hz : F.fl.z ∈ Λ) :
    n F.fl.z - F.fl.z ∈ XLam Λ F :=
  mem_XLam.2 ⟨Submodule.sub_mem _ (autLam_maps hn.1 hz) hz, hn.2.2 _ (z_mem_orth F)⟩

theorem XLam_transport {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} {T₀ : E} {F : LFlag S r T₀}
    (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) :
    XLam Λ F₂ = Formalism.HermitianLatticesTheory.gmap n (XLam Λ F₁) := by
  let g : S.V ≃ₗ[E] S.V := m.trans n
  have hfr' : ∀ a, frame F₂ a = g (frame F₁ a) := fun a => hfr a
  have hg : IsAutLam S Λ g := autLam_mul hn.1 hm.1
  have h1 : XLam Λ F₂ = Formalism.HermitianLatticesTheory.gmap g (XLam Λ F₁) := by
    ext v
    rw [mem_gmap_iff, mem_XLam, mem_XLam, Xsp_mem_transport hfr' v]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨autLam_symm_maps hg h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := autLam_maps hg h1
      simpa using this
  rw [h1]
  show Formalism.HermitianLatticesTheory.gmap (n * m) (XLam Λ F₁) = _
  rw [gmap_mul', gmap_XLam_self hm]

theorem UU_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt)) :
    UU Λ F F₂ = Formalism.HermitianLatticesTheory.gmap n (UU Λ F F₁) := by
  unfold UU
  rw [gmap_sup, gmap_sup, gmap_sup, gmap_span_singleton, gmap_span_singleton, gmap_XLam_self hn,
    ← XLam_transport hn hm hfr, sup_assoc, sup_assoc (XLam Λ F ⊔ _)]
  have e1 : XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} = XLam Λ F ⊔ Submodule.span (𝓞 E) {n F.zt} := by
    refine sup_span_swap ?_
    rw [hF.2]
    have := Submodule.neg_mem _ (nlam_z_sub hn hF.1)
    rwa [neg_sub] at this
  have e2 : XLam Λ F₂ ⊔ Submodule.span (𝓞 E) {F₂.zt} = XLam Λ F₂ ⊔ Submodule.span (𝓞 E) {n F₁.zt} := by
    refine sup_span_swap ?_
    rw [hzt, ← map_sub, XLam_transport hn hm hfr, mem_gmap_iff, LinearEquiv.symm_apply_apply, h₁.2]
    exact nlam_z_sub hm h₁.1
  rw [e1, e2]

theorem spanE_gmap (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    spanE S (Formalism.HermitianLatticesTheory.gmap n M) = (spanE S M).map (n : S.V →ₗ[E] S.V) := by
  unfold spanE
  rw [gmap_eq_map, Submodule.map_coe]
  have e : ⇑(fO n) = ⇑(n : S.V →ₗ[E] S.V) := rfl
  rw [e, Submodule.span_image]

theorem BLat_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt)) :
    BLat Λ F F₂ = Formalism.HermitianLatticesTheory.gmap n (BLat Λ F F₁) := by
  unfold BLat UUE
  rw [UU_transport hF h₁ hn hm hfr hzt, spanE_gmap]
  ext v
  rw [mem_gmap_iff, Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, Submodule.mem_map_equiv]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨autLam_symm_maps hn.1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := autLam_maps hn.1 h1
    simpa using this

theorem locP_BLat_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt))
    (P : Ideal (𝓞 E)) [P.IsPrime] :
    Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₂) = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₁)) := by
  rw [BLat_transport hF h₁ hn hm hfr hzt, locP_gmap]

theorem offg_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt))
    (P : Ideal (𝓞 E)) [P.IsPrime] :
    Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₂) = Formalism.HermitianLatticesTheory.localization₂ P (UU Λ F F₂) ↔
      Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₁) = Formalism.HermitianLatticesTheory.localization₂ P (UU Λ F F₁) := by
  rw [locP_BLat_transport hF h₁ hn hm hfr hzt, UU_transport hF h₁ hn hm hfr hzt, locP_gmap]
  exact ⟨gmap_injective n, fun h => by rw [h]⟩

end Gen

end PI.TermAttrConst.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.SpanFrameLtSucc
section
noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def cg (g : S.V ≃ₗ[E] S.V) (Y : S.V →ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  (g : S.V →ₗ[E] S.V) ∘ₗ Y ∘ₗ (g.symm : S.V →ₗ[E] S.V)

theorem cg_apply (g : S.V ≃ₗ[E] S.V) (Y : S.V →ₗ[E] S.V) (v : S.V) : cg g Y v = g (Y (g.symm v)) := rfl

theorem sum_mem_X (F : FlagG S r T) (c : Fin r → E) :
    (∑ j, c j • F.e j) ∈ Submodule.span E (Set.range F.e) :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem coefX_sum (F : FlagG S r T) (c : Fin r → E) (i : Fin r) : F.coefX (∑ j, c j • F.e j) i = c i := by
  unfold FlagG.coefX
  rw [dif_pos (sum_mem_X F c)]
  rw [F.e_indep.repr_eq (l := Finsupp.equivFunOnFinite.symm c) (x := ⟨_, sum_mem_X F c⟩)
    (by simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype])]
  simp

theorem coefX_add_low (F : FlagG S r T) {v w : S.V} (hv : v ∈ F.X) (i : Fin r) (hw : w ∈ F.Xa i.1) :
    F.coefX (v + w) i = F.coefX v i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hv
  have hw' : w ∈ Submodule.span E (F.e '' {j | j < i}) := hw
  obtain ⟨d, hd0, rfl⟩ := exists_coeffs (S := S) F.e i w hw'
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_smul]
  rw [coefX_sum, coefX_sum, hd0 i (lt_irrefl i), add_zero]

theorem coefX_transport (F₁ : FlagG S r T) (F₂ : FlagG S r T') (g : S.V ≃ₗ[E] S.V)
    (he : ∀ j, F₂.e j = g (F₁.e j)) (v : S.V) (i : Fin r) : F₂.coefX (g v) i = F₁.coefX v i := by
  by_cases hv : v ∈ Submodule.span E (Set.range F₁.e)
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hv
    have : g (∑ j, c j • F₁.e j) = ∑ j, c j • F₂.e j := by simp [he, map_sum, map_smul]
    rw [this, coefX_sum, coefX_sum]
  · have hgv : g v ∉ Submodule.span E (Set.range F₂.e) := by
      intro hm
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hm
      apply hv
      have : v = ∑ j, c j • F₁.e j := by
        apply g.injective
        rw [← hc]
        simp [he, map_sum, map_smul]
      rw [this]
      exact sum_mem_X F₁ c
    unfold FlagG.coefX
    rw [dif_neg hgv, dif_neg hv]

theorem ell_transport (F₁ : FlagG S r T) (F₂ : FlagG S r T') (g : S.V ≃ₗ[E] S.V)
    (hf : ∀ a, F₂.fvec a = g (F₁.fvec a)) (Y : S.V →ₗ[E] S.V) : F₂.ell (cg g Y) = F₁.ell Y := by
  have he : ∀ j, F₂.e j = g (F₁.e j) := fun j => by
    have := hf (Fin.castSucc j)
    simpa [FlagG.fvec] using this
  unfold FlagG.ell
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cg_apply, hf, LinearEquiv.symm_apply_apply]
  exact coefX_transport F₁ F₂ g he (Y (F₁.fvec i.succ)) i

theorem lieN_transport (F₁ : FlagG S r T) (F₂ : FlagG S r T') (g : S.V ≃ₗ[E] S.V)
    (hg : ∀ u v, S.hT (g u) (g v) = S.hT u v)
    (hXa : ∀ a v, v ∈ F₂.Xa a ↔ g.symm v ∈ F₁.Xa a) (hX : ∀ v, v ∈ F₂.X ↔ g.symm v ∈ F₁.X)
    {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F₁.LieN) : cg g Y ∈ F₂.LieN := by
  obtain ⟨hU, hfl, hp⟩ := hY
  have hU' : ∀ u v, S.hT (Y u) v + S.hT u (Y v) = 0 := hU
  have hp' : ∀ x, (∀ u ∈ F₁.X, S.hT u x = 0) → Y x ∈ F₁.X := fun x hx => hp x hx
  show cg g Y ∈ LieU S ∧ (∀ a : ℕ, 1 ≤ a → a ≤ r → ∀ x ∈ F₂.Xa a, cg g Y x ∈ F₂.Xa (a - 1)) ∧
    ∀ x ∈ perpS S F₂.X, cg g Y x ∈ F₂.X
  refine ⟨?_, ?_, ?_⟩
  · show ∀ u v, S.hT (cg g Y u) v + S.hT u (cg g Y v) = 0
    intro u v
    rw [cg_apply, cg_apply]
    have e1 := hg (Y (g.symm u)) (g.symm v)
    have e2 := hg (g.symm u) (Y (g.symm v))
    rw [LinearEquiv.apply_symm_apply] at e1 e2
    rw [e1, e2]
    exact hU' _ _
  · intro a h1 h2 v hv
    rw [hXa, cg_apply, LinearEquiv.symm_apply_apply]
    exact hfl a h1 h2 _ ((hXa a v).1 hv)
  · intro v hv
    have hv' : ∀ u ∈ F₂.X, S.hT u v = 0 := hv
    rw [hX, cg_apply, LinearEquiv.symm_apply_apply]
    refine hp' _ fun u hu => ?_
    have h1 := hv' (g u) ((hX (g u)).2 (by simpa using hu))
    rw [← hg u (g.symm v), LinearEquiv.apply_symm_apply]
    exact h1

theorem maps_iff {U : Submodule E S.V} (n : S.V ≃ₗ[E] S.V) (h : ∀ x ∈ U, n x ∈ U) (v : S.V) :
    v ∈ U ↔ n.symm v ∈ U :=
  ⟨fun hv => symm_mem_of_maps n U h v hv, fun hv => by simpa using h _ hv⟩

theorem Xa_zero (F : FlagG S r T) : F.Xa 0 = ⊥ := by
  simp [FlagG.Xa]

theorem nlam_maps_Xa (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F)
    (a : ℕ) : ∀ x ∈ F.fl.Xa a, n x ∈ F.fl.Xa a := by
  cases a with
  | zero =>
    intro x hx
    rw [Xa_zero] at hx ⊢
    rw [(Submodule.mem_bot E).1 hx, map_zero]
    exact Submodule.zero_mem _
  | succ j => exact nlam_maps_Xflag hn j

theorem lieN_conj_nlam (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F.fl.LieN) : cg n Y ∈ F.fl.LieN :=
  lieN_transport F.fl F.fl n (isom_app hn.1.1) (fun a v => maps_iff n (nlam_maps_Xa Λ hn a) v)
    (fun v => maps_iff n (nlam_maps_X hn) v) hY

theorem z_mem_perp (F : FlagG S r T) : F.z ∈ perpS S F.X := by
  show ∀ x ∈ F.X, S.hT x F.z = 0
  intro x hx
  dsimp only [Formalism.MainNotions.S.FlagG.X] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact F.z_orth i
  | zero => simp
  | add y y' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  | smul c y _ h => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_zero]

theorem X_le_Xa_r (F : FlagG S r T) : F.X ≤ F.Xa r := by
  dsimp only [Formalism.MainNotions.S.FlagG.X, Formalism.MainNotions.S.FlagG.Xa]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨j, j.2, rfl⟩

theorem Yf_mem (F : FlagG S r T) {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F.LieN) (i : Fin r) :
    Y (F.fvec i.succ) ∈ F.Xa (i.1 + 1) := by
  by_cases hi : i.1 + 1 < r
  · let j : Fin r := ⟨i.1 + 1, hi⟩
    have hs : i.succ = Fin.castSucc j := Fin.ext rfl
    have hf : F.fvec i.succ = F.e j := by rw [hs]; simp [FlagG.fvec]
    rw [hf]
    have hj : F.e j ∈ F.Xa (i.1 + 2) := Submodule.subset_span ⟨j, (show j.1 < i.1 + 2 by simp [j]), rfl⟩
    have h := hY.2.1 (i.1 + 2) (by omega) (by omega) (F.e j) hj
    simpa using h
  · have hr : i.1 + 1 = r := by omega
    have hs : i.succ = Fin.last r := Fin.ext (by simp; omega)
    have hf : F.fvec i.succ = F.z := by rw [hs]; simp [FlagG.fvec]
    rw [hf, hr]
    exact X_le_Xa_r F (hY.2.2 _ (z_mem_perp F))

theorem span_frame_lt_succ (F : LFlag S r T) (i : Fin r) :
    Submodule.span E (frame F '' {c | c < i.succ}) ≤ F.fl.Xa (i.1 + 1) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, hc, rfl⟩
  have hc' : c.1 < i.1 + 1 := by
    have := Fin.lt_def.1 hc
    simpa using this
  have hcr : c.1 < r := by omega
  have hce : c = Fin.castSucc ⟨c.1, hcr⟩ := Fin.ext rfl
  rw [hce, frame_castSucc]
  exact Submodule.subset_span ⟨⟨c.1, hcr⟩, hc', rfl⟩

theorem ell_conj_nlam (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F.fl.LieN) : F.fl.ell (cg n Y) = F.fl.ell Y := by
  unfold FlagG.ell
  refine Finset.sum_congr rfl fun i _ => ?_
  have hni : n.symm ∈ NLam Λ F := nlam_inv hn
  have hu : n.symm (frame F i.succ) - frame F i.succ ∈ F.fl.Xa (i.1 + 1) :=
    span_frame_lt_succ F i (nlam_frame Λ hni i.succ)
  have hYf : Y (frame F i.succ) ∈ F.fl.Xa (i.1 + 1) := Yf_mem F.fl hY i
  set v := Y (n.symm (frame F i.succ)) with hvdef
  have hYu : v - Y (frame F i.succ) ∈ F.fl.Xa i.1 := by
    have h := hY.2.1 (i.1 + 1) (by omega) (by omega) _ hu
    rw [map_sub] at h
    simpa using h
  have hvmem : v ∈ F.fl.Xa (i.1 + 1) := by
    have := Submodule.add_mem _ hYf (Xflag_mono F i.1 hYu)
    simpa using this
  have hnv : n v - v ∈ F.fl.Xa i.1 := hn.2.1 i.1 _ hvmem
  have key : n v = Y (frame F i.succ) + ((v - Y (frame F i.succ)) + (n v - v)) := by abel
  show F.fl.coefX (n v) i = F.fl.coefX (Y (frame F i.succ)) i
  rw [key]
  exact coefX_add_low F.fl (Xflag_le_X F _ hYf) i (Submodule.add_mem _ hYu hnv)

theorem rel_fwd (K : Type) [Field K] [Algebra K E] (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T}
    {x y : LFlag S r T'} (h : DCRel Λ F x y) (hx : Relevant K F.fl x.fl) : Relevant K F.fl y.fl := by
  intro Y hY
  obtain ⟨hYF, hYy⟩ := hY
  obtain ⟨n, hn, m, hm, hfr, -⟩ := h
  let g : S.V ≃ₗ[E] S.V := m.trans n
  have hfr' : ∀ a, frame y a = g (frame x a) := fun a => hfr a
  have hgi : ∀ u v, S.hT (g.symm.symm u) (g.symm.symm v) = S.hT u v := by
    intro u v
    rw [LinearEquiv.symm_symm]
    show S.hT (n (m u)) (n (m v)) = S.hT u v
    rw [isom_app hn.1.1, isom_app hm.1.1]
  have hgs : ∀ u v, S.hT (g.symm u) (g.symm v) = S.hT u v := by
    intro u v
    have := hgi (g.symm u) (g.symm v)
    rw [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hni : n.symm ∈ NLam Λ F := nlam_inv hn
  have hY1F := lieN_conj_nlam Λ hni hYF
  have hY1e := ell_conj_nlam Λ hni hYF
  have hXa : ∀ a v, v ∈ x.fl.Xa a ↔ g.symm.symm v ∈ y.fl.Xa a := by
    intro a v
    rw [LinearEquiv.symm_symm]
    exact ⟨fun hv => (Xflag_mem_transport hfr' a (g v)).2 (by simpa using hv),
      fun hv => by simpa using (Xflag_mem_transport hfr' a (g v)).1 hv⟩
  have hX : ∀ v, v ∈ x.fl.X ↔ g.symm.symm v ∈ y.fl.X := by
    intro v
    rw [LinearEquiv.symm_symm]
    exact ⟨fun hv => (Xsp_mem_transport hfr' (g v)).2 (by simpa using hv),
      fun hv => by simpa using (Xsp_mem_transport hfr' (g v)).1 hv⟩
  have hY2 : cg g.symm Y ∈ x.fl.LieN := lieN_transport y.fl x.fl g.symm hgs hXa hX hYy
  have hY2e : x.fl.ell (cg g.symm Y) = y.fl.ell Y := by
    refine ell_transport y.fl x.fl g.symm (fun a => ?_) Y
    have := hfr' a
    simp only [frame] at this
    rw [this, LinearEquiv.symm_apply_apply]
  have hc : cg m (cg g.symm Y) = cg n.symm Y := by
    ext v
    simp only [cg_apply, LinearEquiv.symm_symm]
    show m (m.symm (n.symm (Y (n (m (m.symm v)))))) = n.symm (Y (n v))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hY1x : cg n.symm Y ∈ x.fl.LieN := hc ▸ lieN_conj_nlam Λ hm hY2
  have hY1xe : x.fl.ell (cg n.symm Y) = x.fl.ell (cg g.symm Y) := by
    rw [← hc]
    exact ell_conj_nlam Λ hm hY2
  have key := hx (cg n.symm Y) ⟨hY1F, hY1x⟩
  unfold FlagG.dpsi at key ⊢
  rw [← hY1e, key, hY1xe, hY2e]

theorem relFun_all (K : Type) [Field K] [Algebra K E] (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T)
    (P : LFlag S r T' → Prop) : RelFun Λ F P K := by
  intro x y h
  have h' : DCRel Λ F x.1 y.1 := h
  have hs : DCRel Λ F y.1 x.1 := (dCRelEquivAll_holds E S r T T' Λ F).symm h'
  exact ⟨rel_fwd K Λ h', rel_fwd K Λ hs⟩

end Gen

end PI.TermAttrConst.UnitaryGroupMassFormula
end
end

