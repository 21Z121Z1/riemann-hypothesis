import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0011
import GroundTheory.AutomorphicForms.FiniteBruhat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ContinuousResI
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

theorem res_mem_Dec {σ : G E' Ω} (hσ : σ ∈ Dec (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Dec (F := E) A := by
  rw [mem_Dec] at hσ ⊢
  have key : ∀ x, x ∈ (AlgEquiv.restrictScalars E σ) • A ↔ x ∈ σ • A := by
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  ext x
  rw [key, hσ]

theorem res_mem_Ine {σ : G E' Ω} (hσ : σ ∈ Ine (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Ine (F := E) A :=
  ⟨res_mem_Dec hσ.1, hσ.2⟩

theorem res_actsAs {q q' n a b : ℕ} (hq : q' = q ^ n) {σ : G E' Ω} (hσ : ActsAs A q' σ a b) :
    ActsAs A q (AlgEquiv.restrictScalars E σ) (n * a) (n * b) := by
  refine ⟨res_mem_Dec hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [hq, ← pow_mul, ← pow_mul] at this
  exact this

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

def resW {n : ℕ} (hq : normV w' = normV w ^ n) : Weil h' →* Weil h where
  toFun σ := ⟨AlgEquiv.restrictScalars E (σ : G E' Ω), by
    obtain ⟨a, b, hab⟩ := σ.2
    exact ⟨n * a, n * b, res_actsAs hq hab⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem coe_resW {n : ℕ} (hq : normV w' = normV w ^ n) (σ : Weil h') :
    ((resW h h' hq σ : Weil h) : G E Ω) = AlgEquiv.restrictScalars E (σ : G E' Ω) := rfl

theorem deg_resW {n : ℕ} (hq : normV w' = normV w ^ n) (σ : Weil h') : deg (resW h h' hq σ) = n * deg σ := by
  obtain ⟨a, b, hab⟩ := σ.2
  rw [deg_eq (σ := resW h h' hq σ) (res_actsAs hq hab), deg_eq hab]
  push_cast; ring

def resI : Ine (F := E') A →* Ine (F := E) A where
  toFun t := ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem resW_ineIncl {n : ℕ} (hq : normV w' = normV w ^ n) (t : Ine (F := E') A) :
    resW h h' hq (ineIncl h' t) = ineIncl h (resI t) := rfl

theorem continuous_res : Continuous (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one, Filter.tendsto_def]
  intro U hU
  obtain ⟨F, hF, hFU⟩ : ∃ F : IntermediateField E Ω, FiniteDimensional E F ∧
      (F.fixingSubgroup : Set (Ω ≃ₐ[E] Ω)) ⊆ U := by
    first
      | exact (krullTopology_mem_nhds_one_iff E Ω U).mp hU
      | (obtain ⟨V, hV, hVU⟩ := (galGroupBasis E Ω).nhds_one_hasBasis.mem_iff.mp hU
         obtain ⟨H, ⟨F, hF, rfl⟩, rfl⟩ := (mem_galBasis_iff E Ω V).mp hV
         exact ⟨F, hF, hVU⟩)
  obtain ⟨t, ht⟩ : F.FG := by
    apply IntermediateField.fg_of_fg_toSubalgebra
    apply Subalgebra.fg_of_fg_toSubmodule
    first
      | exact (Submodule.fg_iff_finiteDimensional _).mpr hF
      | exact Module.Finite.iff_fg.mp hF
  have hint : ∀ x ∈ (t : Set Ω), IsIntegral E' x := by
    intro x _
    first
      | exact Algebra.IsIntegral.isIntegral x
      | exact ((IsAlgClosure.isAlgebraic (R := E') (K := Ω)).isAlgebraic x).isIntegral
      | exact (IsAlgClosure.algebraic (R := E') (K := Ω) x).isIntegral
  have hfin : FiniteDimensional E' (IntermediateField.adjoin E' (t : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hle : F ≤ (IntermediateField.adjoin E' (t : Set Ω)).restrictScalars E := by
    rw [← ht, IntermediateField.adjoin_le_iff]
    intro y hy
    exact IntermediateField.subset_adjoin E' (t : Set Ω) hy
  have hopen := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin E' (t : Set Ω))
  refine Filter.mem_of_superset
    (hopen.mem_nhds (IntermediateField.adjoin E' (t : Set Ω)).fixingSubgroup.one_mem) ?_
  intro σ hσ
  apply hFU
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  first
    | exact hσ x (hle hx)
    | exact hσ x ((IntermediateField.mem_restrictScalars E).mp (hle hx))
    | simpa using hσ x (hle hx)

theorem continuous_resI : Continuous (resI (E := E) (E' := E') (Ω := Ω) (A := A)) := by
  apply Continuous.subtype_mk
  exact (continuous_res (E := E) (E' := E') (Ω := Ω)).comp continuous_subtype_val

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFpMat
section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

section Ring

variable {R : Type} [CommRing R]

theorem longElt_mul_self (n : ℕ) : longElt n R * longElt n R = 1 := Units.ext (antidiag_mul_self n R)

theorem invT_val_apply {n : ℕ} (z : GL (Fin n) R) (i j : Fin n) :
    ((GlobalTheory.CuspRep.invT n R z : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      ((z⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j i := rfl

theorem invT_corner {m : ℕ} (y : GL (Fin m) R) :
    GlobalTheory.CuspRep.invT (m + 1) R (corner y) = corner (GlobalTheory.CuspRep.invT m R y) := by
  ext i j
  rw [invT_val_apply, ← corner_inv]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [corner_last_last]
    | cast j => simp [corner_last_cs, corner_cs_last]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [corner_last_cs, corner_cs_last]
    | cast j => rw [corner_cs_cs, corner_cs_cs, invT_val_apply]

theorem tilde_corner {m : ℕ} (y : GL (Fin m) R) :
    tilde (corner y) = longElt (m + 1) R * corner (longElt m R) * corner (tilde y) := by
  simp only [tilde]
  rw [mul_assoc, ← corner_mul, ← mul_assoc (longElt m R), longElt_mul_self, one_mul, invT_corner]

theorem rev_eq_iff' {n : ℕ} (i j : Fin n) : i = j.rev ↔ j = i.rev :=
  ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩

theorem invT_longElt (n : ℕ) : GlobalTheory.CuspRep.invT n R (longElt n R) = longElt n R := by
  ext i j
  rw [invT_val_apply, longElt_inv, val_longElt, val_longElt]
  exact if_congr (rev_eq_iff' i j) rfl rfl

theorem invT_invT {n : ℕ} (y : GL (Fin n) R) : GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R y) = y := by
  ext i j
  rw [invT_val_apply, show (GlobalTheory.CuspRep.invT n R y)⁻¹ = GlobalTheory.CuspRep.invT n R y⁻¹ from (map_inv _ y).symm,
    invT_val_apply, inv_inv]

theorem tilde_tilde {n : ℕ} (y : GL (Fin n) R) : tilde (tilde y) = y := by
  simp only [tilde, map_mul, invT_longElt, invT_invT, ← mul_assoc, longElt_mul_self, one_mul]

theorem conjT_inv {n : ℕ} (u : GL (Fin n) R) :
    longElt n R * GlobalTheory.CuspRep.invT n R u⁻¹ * (longElt n R)⁻¹ =
      (longElt n R * GlobalTheory.CuspRep.invT n R u * (longElt n R)⁻¹)⁻¹ := by
  rw [map_inv]
  group

theorem columnMatrix_sq_zero {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) :
    Matrix.of (fun r k : Fin n => if k = c then a r else 0) * Matrix.of (fun r k : Fin n => if k = c then a r else 0) =
      0 := by
  ext r k
  simp [Matrix.mul_apply, ha]

def colElt {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) : GL (Fin n) R :=
  ⟨1 + Matrix.of (fun r k => if k = c then a r else 0), 1 - Matrix.of (fun r k => if k = c then a r else 0),
    by rw [add_mul, one_mul, mul_sub, mul_one, columnMatrix_sq_zero a c ha, sub_zero]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, columnMatrix_sq_zero a c ha, add_zero]; abel⟩

theorem colElt_val {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) :
    (colElt a c ha : Matrix (Fin n) (Fin n) R) = 1 + Matrix.of (fun r k => if k = c then a r else 0) := rfl

theorem colElt_apply {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) (r k : Fin n) :
    (colElt a c ha : Matrix (Fin n) (Fin n) R) r k = (1 : Matrix (Fin n) (Fin n) R) r k + if k = c then a r else 0 :=
  rfl

theorem colElt_mem {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) (h : ∀ r, c < r → a r = 0) :
    colElt a c ha ∈ unipB R (Fin n) := by
  refine (mem_unipB R).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [colElt_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    by_cases hj : j = c
    · subst hj; simp [h i hji]
    · simp [hj]
  · rw [colElt_apply, Matrix.one_apply_eq]
    by_cases hi : i = c
    · subst hi; simp [ha]
    · simp [hi]

theorem superDiag_colElt {m : ℕ} (a : Fin (m + 1) → R) (i : Fin m) (ha : a i.succ = 0) :
    superDiag (colElt a i.succ ha) = a i.castSucc := by
  have key : ∀ r k : Fin (m + 1), (if k.val = r.val + 1 then (colElt a i.succ ha : Matrix (Fin (m + 1)) (Fin (m + 1)) R) r k
      else 0) = if r = i.castSucc then (if k = i.succ then a r else 0) else 0 := by
    intro r k
    rw [colElt_apply]
    by_cases h1 : k.val = r.val + 1
    · have hrk : r ≠ k := fun h => by rw [h] at h1; omega
      rw [if_pos h1, Matrix.one_apply_ne hrk, zero_add]
      by_cases h2 : k = i.succ
      · have : r = i.castSucc := Fin.ext (by rw [h2, Fin.val_succ] at h1; rw [Fin.val_castSucc]; omega)
        rw [if_pos this]
      · rw [if_neg h2]; split_ifs <;> rfl
    · rw [if_neg h1]
      by_cases h3 : r = i.castSucc
      · by_cases h2 : k = i.succ
        · exact absurd (by rw [h2, h3, Fin.val_succ, Fin.val_castSucc]) h1
        · rw [if_pos h3, if_neg h2]
      · rw [if_neg h3]
  simp only [superDiag, Finset.sum_filter, key]
  simp

theorem colElt_comm {n : ℕ} (Y : GL (Fin n) R) (c j : Fin n) (s : R)
    (hrow : ∀ k, (Y : Matrix (Fin n) (Fin n) R) c k = (1 : Matrix (Fin n) (Fin n) R) c k)
    (h1 : s * (Y : Matrix (Fin n) (Fin n) R) c j = 0) (h2 : (Pi.single j s : Fin n → R) c = 0) :
    colElt (fun r => s * (Y : Matrix (Fin n) (Fin n) R) r j) c h1 * Y = Y * colElt (Pi.single j s) c h2 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, colElt_val, colElt_val, add_mul, mul_add, one_mul, mul_one]
  congr 1
  ext r k
  simp only [Matrix.mul_apply, Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [hrow]
  by_cases hk : k = c
  · subst hk
    simp [Pi.single_apply, Matrix.one_apply_eq]
    ring
  · simp [hk, Matrix.one_apply_ne (Ne.symm hk)]

theorem eq_one_of_unip_lower {n : ℕ} {g : GL (Fin n) R} (hu : g ∈ unipB R (Fin n))
    (hb : ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) R) i j = 0) : g = 1 := by
  have h := (mem_unipB R).1 hu
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hb i j hij, Units.val_one, Matrix.one_apply_ne (ne_of_lt hij)]
  · rw [h.2 i, Units.val_one, Matrix.one_apply_eq]
  · rw [h.1 i j hij, Units.val_one, Matrix.one_apply_ne (ne_of_gt hij)]

end Ring

section Field

variable {k : Type} [Field k]

variable (k) in

def lowB (n : ℕ) : Subgroup (GL (Fin n) k) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) k).BlockTriangular OrderDual.toDual}
  mul_mem' {a b} ha hb := by
    show ((a * b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular _
    rw [Units.val_mul]
    exact BlockTriangular.mul ha hb
  one_mem' := by
    show ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular _
    rw [Units.val_one]
    exact blockTriangular_one
  inv_mem' {a} ha := by
    show ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular _
    rw [Matrix.coe_units_inv]
    let _ := (Units.isUnit a).invertible
    exact blockTriangular_inv_of_blockTriangular ha

theorem mem_lowB {n : ℕ} {g : GL (Fin n) k} :
    g ∈ lowB k n ↔ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) k) i j = 0 :=
  ⟨fun h i j hij => h hij, fun h _ _ hij => h _ _ hij⟩

theorem longElt_eq_permGL (n : ℕ) : longElt n k = GroundTheory.Automorphic.permGL k Fin.revPerm := by
  ext i j
  rw [GroundTheory.Automorphic.permGL_apply, val_longElt, Fin.revPerm_apply]
  exact if_congr (rev_eq_iff' j i) rfl rfl

theorem permConj_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : GL (Fin n) k) (r c : Fin n) :
    (((GroundTheory.Automorphic.permGL k σ)⁻¹ * M * GroundTheory.Automorphic.permGL k σ : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) r c = (M : Matrix (Fin n) (Fin n) k) (σ r) (σ c) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply,
    GroundTheory.Automorphic.permGL_mul_apply, inv_inv]

theorem exists_descent {k' : ℕ} (π : Equiv.Perm (Fin (k' + 1))) (h : π ≠ 1) :
    ∃ i : Fin k', π i.succ < π i.castSucc := by
  by_contra hne
  push_neg at hne
  have hmono : StrictMono π := Fin.strictMono_iff_lt_succ.2 fun i =>
    lt_of_le_of_ne (hne i) (π.injective.ne (ne_of_lt Fin.castSucc_lt_succ))
  have hle : ∀ x, x ≤ π x := fun x => hmono.le_apply
  apply h
  have : π⁻¹ = 1 := GroundTheory.Automorphic.perm_eq_one_of_forall_le π⁻¹ fun y => by
    have := hle (π⁻¹ y)
    simpa using this
  exact inv_eq_one.mp this

end Field

end DiscreteGroups.sglob.DzFp
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalSplit
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands TensorProduct Module

namespace DiscreteGroups.sglob.DzType

section Split

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem gsplit_tensor_sum {V V' V'' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [AddCommGroup V''] [Module ℂ V'']
    [FiniteDimensional ℂ V''] (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    (a.tensor (b.sum c)).Iso ((a.tensor b).sum (a.tensor c)) := by
  refine ⟨TensorProduct.prodRight ℂ ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => obtain ⟨y1, y2⟩ := y; simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => obtain ⟨y1, y2⟩ := y; simp
    | add x y hx hy => simp only [map_add, hx, hy]

theorem gsplit_lpChar_lpSum (x y z : WD h) :
    x.lpChar (y.lpSum z) = (x.lpChar y).lpSum (x.lpChar z) := by
  obtain ⟨n1, a, rfl⟩ := x.exists_rep
  obtain ⟨n2, b, rfl⟩ := y.exists_rep
  obtain ⟨n3, c, rfl⟩ := z.exists_rep
  rw [WD.lpSum_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpSum_mk]
  exact WD.sound (gsplit_tensor_sum a b c)

def gsplitEquiv (n : ℕ) : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin 1 → ℂ) × (Fin n → ℂ) where
  toFun v := (fun _ => v 0, fun j => v j.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := Fin.cons (p.1 0) p.2
  left_inv v := Fin.cons_self_tail v
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · rw [Subsingleton.elim i 0]
      simp
    · simp

theorem gsplitEquiv_apply (n : ℕ) (v : Fin (n + 1) → ℂ) :
    gsplitEquiv n v = (fun _ => v 0, fun j => v j.succ) := rfl

theorem gsplit_diag_succ {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    WD.mk (WDRep.diag h c) =
      (WD.lpOfChar h (unrChar h (c 0)) (isSmooth_unrChar h _)).lpSum
        (WD.mk (WDRep.diag h fun j : Fin n => c j.succ)) := by
  rw [WD.lpOfChar, WD.lpSum_mk]
  refine WD.sound ⟨gsplitEquiv n, fun σ v => ?_, fun v => ?_⟩
  · refine Prod.ext (funext fun i => ?_) (funext fun j => ?_) <;> simp [gsplitEquiv_apply]
  · simp only [gsplitEquiv_apply, WDRep.diag_N, WDRep.sum_N, WDRep.ofChars_N, LinearMap.zero_apply,
      LinearMap.prodMap_apply]
    rfl

theorem lpSum_self_of_dim_zero (y : WD h) (hy : y.lpDim = 0) : y.lpSum y = y := by
  obtain ⟨m, a, rfl⟩ := y.exists_rep
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hy
  subst hy
  rw [WD.lpSum_mk]
  exact WD.sound ⟨LinearEquiv.ofFinrankEq _ _ (by simp), fun _ _ => Subsingleton.elim _ _,
    fun _ => Subsingleton.elim _ _⟩

theorem epsilon_eq_one_of_dim_zero {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (y : WD h) (hy : y.lpDim = 0) : ε E w h ψ y = 1 := by
  have h1 := hε.add E w h ψ hψ hψ1 y y
  rw [lpSum_self_of_dim_zero y hy] at h1
  exact mul_left_cancel (a := ε E w h ψ y) (by rw [mul_one]; exact h1.symm)

theorem lpChar_diag_dim_zero (x : WD h) (c : Fin 0 → ℂˣ) : (x.lpChar (WD.mk (WDRep.diag h c))).lpDim = 0 := by
  obtain ⟨m, a, rfl⟩ := x.exists_rep
  rw [WD.lpChar_mk, WD.lpDim_mk, Module.finrank_tensorProduct]
  simp

theorem gsplit_eps {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (x : WD h) :
    ∀ (n : ℕ) (c : Fin n → ℂˣ), ε E w h ψ (x.lpChar (WD.mk (WDRep.diag h c))) =
      ∏ j, ε E w h ψ (x.lpTwist (unrChar h (c j)) (isSmooth_unrChar h (c j)))
  | 0, c => by
    rw [Fin.prod_univ_zero]
    exact epsilon_eq_one_of_dim_zero hε ψ hψ hψ1 _ (lpChar_diag_dim_zero x c)
  | n + 1, c => by
    rw [gsplit_diag_succ, gsplit_lpChar_lpSum, hε.add E w h ψ hψ hψ1, lpChar_lpOfChar,
      gsplit_eps hε ψ hψ hψ1 x n, Fin.prod_univ_succ]

end Split

theorem eps_unr_split {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (u : WD h) (hu : u.unr) :
    ∃ c : Fin u.lpDim → ℂˣ, ∀ ε : EpsFamily A, IsDeligneEps ε →
      ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
      ∀ x : WD h, ε E w h ψ (x.lpChar u) =
        ∏ j, ε E w h ψ (x.lpTwist (unrChar h (c j)) (isSmooth_unrChar h (c j))) := by
  obtain ⟨n, c, rfl⟩ := Unram.exists_diag hu
  have hn : (WD.mk (WDRep.diag h c)).lpDim = n := by rw [WD.lpDim_mk, Module.finrank_fin_fun]
  refine ⟨fun j => c (Fin.cast hn j), fun ε hε ψ hψ hψ1 x => ?_⟩
  rw [gsplit_eps hε ψ hψ hψ1 x n c]
  exact (Fintype.prod_equiv (finCongr hn) _ _ fun j => rfl).symm

end DiscreteGroups.sglob.DzType
end
end

