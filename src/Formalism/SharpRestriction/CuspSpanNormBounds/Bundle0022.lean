import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0021

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.GramProductLeHeightBoundTwo
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem two_le_b (s : Scale) : 2 ≤ s.b := by
  unfold Scale.b Scale.L
  have h1 : 1 ≤ s.x ^ s.eps := Real.one_le_rpow (le_of_lt s.one_lt_alt) s.eps_pos.le
  have h2 := Real.add_one_le_exp (s.x ^ s.eps)
  linarith

theorem T_le_of_hyp {D : D7} {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C' Cl Cg cb Cu cT CT C0 A : ℝ}
    (hH : Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) (w : D.what₂.Word) :
    ((Tu D w : ℕ) : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := by
  obtain ⟨⟨hS0, -, -⟩, -⟩ := hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h23, -, -⟩ := hS0
  exact (h23 w).2

section Bound

variable (D : D7) (u u' : D.what₂.Word)

def Pt (b C : ℝ) (Z : GramM D) (τ : D.what₂.Tau) : ℝ :=
  ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))

theorem sizeZ_eq (b C : ℝ) (Z : GramM D) : Cnt.sizeZ D b C Z = ∏ τ, Pt D b C Z τ := rfl

theorem absDl_le_Pt {b C : ℝ} (hb : 0 < b) (Z : GramM D) (τ : D.what₂.Tau) {l : ℕ}
    (hl : l ∈ Finset.Icc 1 (D.R.rS + 1)) :
    Cnt.absDl D Z l τ ≤ b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ := by
  have hH2 : 0 < b ^ (C * (D.R.m : ℝ) ^ 2) := Real.rpow_pos_of_pos hb _
  calc Cnt.absDl D Z l τ
      = b ^ (C * (D.R.m : ℝ) ^ 2) * (Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := by field_simp
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2) * max 1 (Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hH2.le
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_prod_max hl (fun l => Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))) hH2.le

theorem gram_product_le_height_bound_two (Z : GramM D) {b C CT : ℝ} (hb : 2 ≤ b) (h1T : 1 ≤ ((Tu D u : ℕ) : ℝ))
    (hT : ((Tu D u : ℕ) : ℝ) ≤ b ^ (CT * (D.R.m : ℝ))) (hT' : ((Tu D u' : ℕ) : ℝ) ≤ b ^ (CT * (D.R.m : ℝ)))
    (hr : 1 ≤ D.R.rS) (hC : 3 + 2 * |CT| ≤ C) : localGramProduct D u u' Z ≤ Cnt.HHZ D b C Z := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hH2 : 0 < b ^ (C * (D.R.m : ℝ) ^ 2) := Real.rpow_pos_of_pos hb0 _
  have hβ1 : 1 ≤ b ^ (CT * (D.R.m : ℝ)) := h1T.trans hT
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hP1 : ∀ τ, 1 ≤ Pt D b C Z τ := fun τ => one_le_prod_max _ _
  have hr1 : D.R.rS + 1 ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  have hr0 : D.R.rS ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨hr, by omega⟩

  have hG : ∀ τ, |Cnt.Gz D (Tu D u) (Tu D u') Z τ| ≤
      2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 := by
    intro τ
    have ha0 := absDl_nonneg D Z (D.R.rS + 1) τ
    have hd0 := absDl_nonneg D Z D.R.rS τ
    have ha := absDl_le_Pt D (C := C) hb0 Z τ hr1
    have hd := absDl_le_Pt D (C := C) hb0 Z τ hr0
    have hX0 : 0 ≤ (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 := sq_nonneg _
    have ha2 := pow_le_pow_left₀ ha0 ha 2
    have hd2 := pow_le_pow_left₀ hd0 hd 2
    have hc0 : 0 ≤ ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) := by positivity
    have hc : ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) ≤ (b ^ (CT * (D.R.m : ℝ))) ^ 2 := by
      rw [sq]; exact mul_le_mul hT hT' (Nat.cast_nonneg _) (by linarith)
    have hβ2 : 1 ≤ (b ^ (CT * (D.R.m : ℝ))) ^ 2 := one_le_pow₀ hβ1
    have hcd : ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) * Cnt.absDl D Z D.R.rS τ ^ 2 ≤
        (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 :=
      mul_le_mul hc hd2 (sq_nonneg _) (by positivity)
    have hcd0 : 0 ≤ ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) * Cnt.absDl D Z D.R.rS τ ^ 2 := by positivity
    have hXβ : (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 ≤
        (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 :=
      le_mul_of_one_le_left hX0 hβ2
    have hβX : 0 ≤ (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 := by positivity
    unfold Cnt.Gz
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Cnt.absDl D Z (D.R.rS + 1) τ)]

  have hprod : |∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ| ≤
      (2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f * (Cnt.sizeZ D b C Z) ^ 2 := by
    rw [Finset.abs_prod]
    calc (∏ τ, |Cnt.Gz D (Tu D u) (Tu D u') Z τ|)
        ≤ ∏ τ, 2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 :=
          Finset.prod_le_prod (fun τ _ => abs_nonneg _) (fun τ _ => hG τ)
      _ = _ := by
          rw [sizeZ_eq, ← D.what₂.card_Tau]
          simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
          ring

  have hexp : (2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f ≤
      (b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) := by
    have e1 : 2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 ≤
        b ^ (1 + CT * (D.R.m : ℝ) * 2 + C * (D.R.m : ℝ) ^ 2 * 2) := by
      rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_one, Real.rpow_mul hb0.le (CT * (D.R.m : ℝ)) 2,
        Real.rpow_mul hb0.le (C * (D.R.m : ℝ) ^ 2) 2, Real.rpow_two, Real.rpow_two]
      have : 0 ≤ (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 := by positivity
      nlinarith
    have hCT : CT ≤ |CT| := le_abs_self CT
    have hCT0 : 0 ≤ |CT| := abs_nonneg CT
    have k1 : 4 ≤ C * (D.R.m : ℝ) - 2 := by nlinarith
    have k2 : 1 + 2 * |CT| * (D.R.m : ℝ) ≤ C * (D.R.m : ℝ) ^ 2 := by nlinarith
    have k3 : 1 + CT * (D.R.m : ℝ) * 2 + C * (D.R.m : ℝ) ^ 2 * 2 ≤ C * (D.R.m : ℝ) ^ 2 * (C * (D.R.m : ℝ)) := by
      have hCm2 : 0 ≤ C * (D.R.m : ℝ) ^ 2 := by nlinarith
      nlinarith
    calc (2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f
        ≤ (b ^ (1 + CT * (D.R.m : ℝ) * 2 + C * (D.R.m : ℝ) ^ 2 * 2)) ^ D.R.f :=
          pow_le_pow_left₀ (by positivity) e1 _
      _ = b ^ ((1 + CT * (D.R.m : ℝ) * 2 + C * (D.R.m : ℝ) ^ 2 * 2) * D.R.f) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
      _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * (D.R.m : ℝ))) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1
          have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
          nlinarith
      _ = _ := Real.rpow_mul hb0.le _ _
  have hs1 := one_le_sizeZ D b C Z
  have h5 : (Cnt.sizeZ D b C Z) ^ 2 ≤ (Cnt.sizeZ D b C Z) ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  have hg0 : 0 ≤ ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f) := by positivity
  have hg : ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f) ≤ 1 :=
    pow_le_one₀ (inv_nonneg.2 (Nat.cast_nonneg _)) (Nat.cast_inv_le_one (gS D))
  unfold localGramProduct Cnt.HHZ
  calc (∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)
      ≤ |∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ| * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hg0
    _ ≤ |∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ| := mul_le_of_le_one_right (abs_nonneg _) hg
    _ ≤ _ := hprod
    _ ≤ (b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) * (Cnt.sizeZ D b C Z) ^ 2 :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)

end Bound

section Fam

def LatticeIdentityGeneric : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ),
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' (ZhatL (lf D F0) F')

theorem gram_flag_of_identity (hI : LatticeIdentityGeneric) (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)
    {C' Cl Cg cb Cu cT CT C0 A C : ℝ} (hC : 3 + 2 * |CT| ≤ C) :
    GenericTermDetProductBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro hH F0 he hz0 Λ hΛr Z _ F' hT' hgen hZE
  have hid := hI D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz0 Λ hΛr F' hT' hgen
  have hone := one_le_generic_gram_value D large₂ u u' hH F0 he hz0 Λ hΛr F' hT' hgen
  have hZ : localGramProduct D u u' Z = localGramProduct D u u' (ZhatL (lf D F0) F') := gram_product_equiv_invariant D u u' hZE
  have hSt : Cnt.Stand D u u' := hH.2.1
  have h3 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hSt.2.2.2.1
  refine ⟨hid.trans hZ.symm, ?_, gram_product_le_height_bound_two D u u' Z (two_le_b large₂.sc) (by linarith) (T_le_of_hyp hH u)
    (T_le_of_hyp hH u') hSt.1 hC⟩
  rw [hZ, ← hid]
  exact hone

theorem gram_flag_family_of_identity (hI : LatticeIdentityGeneric) {eps : ℝ} (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ) :
    FamilyGenericTermDetProductBound Fm Cg cb Cu cT CT C0 A :=
  ⟨3 + 2 * |CT|, fun _ hC => ⟨0, fun x _ i u u' => gram_flag_of_identity hI (Fm.D x i) (Fm.L x i) u u' hC⟩⟩

end Fam

end Formalism.MainNotions.GramProductBounds

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfLocalDiscriminant
section
noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem natCast_repr (p : Ideal (𝓞 E)) (T : ℕ) (hT : T.Prime) (hN : Ideal.absNorm p = T) (x : 𝓞 E) :
    ∃ n : ℕ, x - (n : 𝓞 E) ∈ p := by
  have hc : Nat.card (𝓞 E ⧸ p) = T := by rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]
  have : Finite (𝓞 E ⧸ p) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hT.ne_zero)
  let _ := Fintype.ofFinite (𝓞 E ⧸ p)
  have : NeZero T := ⟨hT.ne_zero⟩
  have hc' : Fintype.card (𝓞 E ⧸ p) = T := by rw [Fintype.card_eq_nat_card, hc]
  let e := ZMod.ringEquivOfPrime (𝓞 E ⧸ p) hT hc'
  obtain ⟨k, hk⟩ := e.surjective (Ideal.Quotient.mk p x)
  refine ⟨k.val, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_natCast, ← hk, ← map_natCast e k.val,
    ZMod.natCast_zmod_val, sub_self]

theorem split_conj_ne (hc : Formalism.BasicNotions.CMData F E) (T : ℕ) (hT : T.Prime) (hsp : Formalism.MainNotions.S.SplitsCompl E T)
    (p : Ideal (𝓞 E)) (hp : p.IsMaximal) (hTp : ((T : ℕ) : 𝓞 E) ∈ p) : conjIdeal (K := E) p ≠ p := by
  intro hconj
  have hu : IsCMUnram E := hc.cmUnram
  unfold IsCMUnram at hu
  obtain ⟨_, _, h3⟩ := hu
  obtain ⟨θ, t, hθt, hnot⟩ := h3 p hp
  apply hnot
  obtain ⟨n, hn⟩ := natCast_repr p T hT (hsp p hp hTp).1 θ
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ s : 𝓞 E, algebraMap (𝓞 E) E (σ s) = star (algebraMap (𝓞 E) E s) := fun s => rfl
  have hσp : ∀ s ∈ p, σ s ∈ p := by
    intro s hs
    rw [← hconj]
    unfold conjIdeal
    exact Ideal.subset_span ⟨s, hs, hσ s⟩
  have hσθ : σ θ = t := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [hσ, hθt]
  have h2 : σ (θ - (n : 𝓞 E)) ∈ p := hσp _ hn
  rw [map_sub, map_natCast, hσθ] at h2
  have e : θ - t = (θ - (n : 𝓞 E)) - (t - (n : 𝓞 E)) := by ring
  rw [e]
  exact p.sub_mem hn h2

theorem unimodAt_of_unimod {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (hlat : Submodule.IsLattice E L) (hu : IsUnimodular h L)
    (p : Ideal (𝓞 E)) : IsUnimodularAt h p L := by
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective _ _
  have hst : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
    fun r => cyc_star_int r
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (self := hlat)
  unfold IsUnimodularAt
  rw [locDual_dualAt_loc h hinj hst]
  have e1 := locDual_loc_dual_le h p L
  have e2 := locDual_dualAt_le h hst p L hfg
  unfold IsUnimodular at hu
  rw [hu] at e1 e2
  exact le_antisymm e2 e1

theorem unimod_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (L M : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (hM : Submodule.IsLattice E M)
    (huL : IsUnimodular S.hT L) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT L :=
  ⟨hM, fun p hp => hU F E hc S L M hL hM p hp (unimodAt_of_unimod S.hT L hL huL p) (unimodAt_of_unimod S.hT M hM huM p)⟩

theorem unimodular_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (M : Submodule (𝓞 E) S.V) (hM : Submodule.IsLattice E M) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT S.L0 :=
  unimod_mem_genus hU hc S S.L0 M S.standardTuple_isLattice hM S.baseLattice_isUnimodular huM

end Conj

def CycLocType : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L : Submodule (𝓞 E) S.V, IsCycT S.hT T L →
    ∀ p : Ideal (𝓞 E), p.IsMaximal → ((T : ℕ) : 𝓞 E) ∈ p → LocTypeAt S.hT p L

theorem cycSplitAt_of (h : CycLocType) : CycSplitAt :=
  fun F E _ _ _ _ _ _ hc S T hT hT3 hsp L hL p hp hTp =>
    ⟨split_conj_ne hc T hT hsp p hp hTp, h F E hc S T hT hT3 hsp L hL p hp hTp⟩

section Rows

open Formalism.BasicNotions Formalism.MainNotions.BridgeLemma₂

theorem rows_one_genus_of_local_discriminant (hL : CycLocType) (hU : LocUnimod) (hS : LocSplitType) (D : D7) (u : D.what₂.Word) :
    OrthLatticesOneGenus D u :=
  rows_one_genus_of_local (cycSplitAt_of hL) hU hS D u

end Rows

end Formalism.MainNotions.BridgeRowsGenus

end
end

