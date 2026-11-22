import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoubleCosetRepsConjugateLevelGroups
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Classical

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem cbe_iff {k : Type} [CommRing k] {n c : ℕ} (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)))
    {r h' κ s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.R1 k n c) (hκ : κ ∈ J) :
    s ∈ Loc.Cbe J (r * h' * κ) ↔ r⁻¹ * s * r ∈ Loc.Cbe J h' := by
  constructor
  · rintro ⟨hs1, hs2⟩
    refine ⟨(Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem ((Loc.R1 k n c).inv_mem hr) hs1) hr, ?_⟩
    have h2 : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J := hs2
    show h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J
    have e : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ = κ * ((r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹) * κ⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hκ h2) (inv_mem hκ)
  · rintro ⟨hs1, hs2⟩
    have hs1' : s ∈ Loc.R1 k n c := by
      have := (Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem hr hs1) ((Loc.R1 k n c).inv_mem hr)
      rwa [show r * (r⁻¹ * s * r) * r⁻¹ = s by group] at this
    refine ⟨hs1', ?_⟩
    have h2 : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J := hs2
    show (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J
    have e : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ = κ⁻¹ * (h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹) * κ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hκ) h2) hκ

theorem red_conj {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (δ : GLint E n P) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ GLint E n P) {A : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hA : ∀ y ∈ stdAt E n P, redV P (g y) = A.1.mulVec (redV P y)) :
    ∀ y ∈ stdAt E n P, redV P ((δ.1 * g * δ.1⁻¹) y) =
      (GlobalTheory.TopStep.redGL n P δ * A * (GlobalTheory.TopStep.redGL n P δ)⁻¹).1.mulVec (redV P y) := by
  intro y hy
  have h1 : δ.1⁻¹ y ∈ stdAt E n P := ((δ⁻¹).2 y).2 hy
  have h2 : g (δ.1⁻¹ y) ∈ stdAt E n P := (hg _).2 h1
  show redV P (δ.1 (g (δ.1⁻¹ y))) = _
  rw [GlobalTheory.TopStep.redV_redGL δ h2, hA _ h1]
  have h3 := GlobalTheory.TopStep.redV_redGL δ⁻¹ hy
  have e : (δ⁻¹).1 y = δ.1⁻¹ y := rfl
  rw [e] at h3
  rw [h3, map_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem inX_mem_lamYat_iff {X : Fields} {Pr : Primes X} {R : Ranks} (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ Pr.vGs) (x : Sp X.E (R.N j)) :
    Loc.inX X.E (R.N j) (cOf R j) x ∈ lamYat (Pr := Pr) (R := R) j P ↔ x ∈ stdAt X.E (R.N j) P := by
  unfold lamYat
  rw [if_pos hP]
  exact ⟨fun hx => by simpa only [GlobalTheory.CongLevel.resX_inX] using GlobalTheory.CongLevel.resX_mem P _ _ _ _ hx,
    GlobalTheory.CongLevel.inX_mem_lamY P _ _ _ x⟩

theorem lamRow_tup {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ}
    (mu mu' : Tup X.F X.E X.K S) (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (f : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) :
    lamRow Ch mu true j P f = lamRow Ch mu' true j P f := by
  unfold lamRow
  simp only [if_pos hP, if_true]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem loc_match : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu mu' : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (cst' : LocCst X (rowSG Pr sel mu')) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (L' : ChIdx X Pr R (QE sel (mu' : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → cst.sharp = true → cst'.sharp = true → L.Ok Ch sel mu cst G m2 → L'.Ok Ch sel mu' cst' G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (b' : L'.β j) (w : {w // w ∈ Pr.vGs}) (r κ : AutY X R j), r ∈ Loc.R1 X.E (R.N j) (cOf R j) → κ ∈ Jat (Pr := Pr) true j w.1 → L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ → ∃ x : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), (r = 1 → x = 1) ∧ (∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), hbar ∈ (L.levG j b w).H ↔ x * hbar * x⁻¹ ∈ (L'.levG j b' w).H) ∧ ∀ (hbar : ↥(L.levG j b w).H) (hbar' : ↥(L'.levG j b' w).H), hbar'.1 = x * hbar.1 * x⁻¹ → (L.levG j b w).lam hbar = (L'.levG j b' w).lam hbar' := by
  intro X Pr R Ch sel S mu mu' cst cst' L L' G m2 _ _ _ hs hs' hok hok' j hj b b' w r κ hr hκ he
  have hP : w.1 ∈ Pr.vGs := w.2
  have hjm : j < R.m := by rw [hok.hm]; omega
  have hG := hok.grpG j b w
  have hG' := hok'.grpG j b' w
  have hC := hok.chrG j b w
  have hC' := hok'.chrG j b' w
  have hint := hok.int j b ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hint' := hok'.int j b' ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hst := hok.stabG j b ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hst' := hok'.stabG j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hpsi := fun a ha => hok.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  have hpsi' := fun a ha => hok'.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  rw [hs] at hG hC hint
  rw [hs'] at hG' hC' hint'
  unfold chiInv at hC hC'
  rw [hs] at hC
  rw [hs'] at hC'
  generalize L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = h at hG hC hint hst he
  generalize L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ = h' at hG' hC' hint' hst' he
  subst he

  have hκs := jat_le_stab_lamY true j w.1 hP κ hκ
  have hrs : r ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j w.1) := by
    have := mul_mem (mul_mem hst (inv_mem hκs)) (inv_mem hst')
    rwa [show r * h' * κ * κ⁻¹ * h'⁻¹ = r by group] at this
  obtain ⟨γ, hγ⟩ := GlobalTheory.QNormal.exists_res hr
  have hγint : γ ∈ GLint X.E (R.N j) w.1 := by
    intro y
    rw [← inX_mem_lamYat_iff (Pr := Pr) j hP, ← inX_mem_lamYat_iff (Pr := Pr) j hP, ← hγ y]
    exact hrs _
  set γg : GLint X.E (R.N j) w.1 := ⟨γ, hγint⟩ with hγg
  refine ⟨GlobalTheory.TopStep.redGL (R.N j) w.1 γg⁻¹, ?_, ?_, ?_⟩
  · intro h1
    subst h1
    have e : γ = 1 := by
      refine LinearEquiv.ext fun y => GlobalTheory.QNormal.inX_injective (c := cOf R j) ?_
      rw [← hγ y]
      rfl
    have e2 : γg = 1 := Subtype.ext e
    rw [e2, inv_one, map_one]
  · intro hbar
    rw [hG, hG']
    constructor
    · rintro ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩
      refine ⟨γ⁻¹ * g * γ, ⟨r⁻¹ * r₁ * r, (cbe_iff _ hr hκ).1 hr₁, GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres⟩, ?_⟩
      intro y hy
      exact red_conj γg⁻¹ (hint ⟨r₁, hr₁, hres⟩) hred y hy
    · rintro ⟨g', ⟨r₁', hr₁', hres'⟩, hred'⟩
      have hγ' : ∀ y, r⁻¹ (Loc.inX X.E (R.N j) (cOf R j) y) = Loc.inX X.E (R.N j) (cOf R j) (γ⁻¹ y) := by
        intro y
        show r.symm _ = _
        rw [LinearEquiv.symm_apply_eq, hγ]
        show _ = Loc.inX X.E (R.N j) (cOf R j) (γ (γ.symm y))
        rw [LinearEquiv.apply_symm_apply]
      have hmem : r * r₁' * r⁻¹ ∈ Loc.Cbe (Jat (Pr := Pr) true j w.1) (r * h' * κ) := by
        refine (cbe_iff _ hr hκ).2 ?_
        rwa [show r⁻¹ * (r * r₁' * r⁻¹) * r = r₁' by group]
      refine ⟨γ * g' * γ⁻¹, ⟨r * r₁' * r⁻¹, hmem, fun y => GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ' hres' y⟩, ?_⟩
      intro y hy
      have e : ∀ (Q A : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), Q * (Q⁻¹ * A * Q⁻¹⁻¹) * Q⁻¹ = A := by
        intro Q A
        group
      have := red_conj γg (hint' ⟨r₁', hr₁', hres'⟩) hred' y hy
      rw [map_inv, e] at this
      exact this
  · intro hbar hbar' hx
    obtain ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩ := (hG hbar.1).1 hbar.2
    have hgint := hint ⟨r₁, hr₁, hres⟩
    have hr₁' := (cbe_iff _ hr hκ).1 hr₁
    have hres' := GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres
    have hred' : ∀ y ∈ stdAt X.E (R.N j) w.1, redV w.1 ((γ⁻¹ * g * γ) y) = hbar'.1.1.mulVec (redV w.1 y) := by
      intro y hy
      rw [hx]
      exact red_conj γg⁻¹ hgint hred y hy
    have e1 := hC hbar g r₁ hr₁ hres hred
    have e2 := hC' hbar' (γ⁻¹ * g * γ) (r⁻¹ * r₁ * r) hr₁' hres' hred'
    refine Units.ext ?_
    rw [e1, e2, GlobalTheory.Proof.level_eq_parahoric_category.n1Arg_conj_eq hr hr₁.1]

    have hr₁s : r₁ ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) := by
      have h1 : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁.2
      have h2 := jat_le_stab_lamY true j w.1 hP _ h1
      have h3 := mul_mem (mul_mem hst h2) (inv_mem hst)
      rw [show r * h' * κ * ((r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹) * (r * h' * κ)⁻¹ = r₁ by group] at h3
      unfold lamYat at h3
      rw [if_pos hP] at h3
      exact h3
    have hq := GlobalTheory.TopStep.qOf_ne_zero (P := w.1) (E := X.E)
    have hia := GlobalTheory.Mem.LevFin.intAt_n1Arg_G hq r₁ hr₁s
    have ea : ((qOf w.1 : ℕ) : X.E) * Loc.n1Arg r₁ / ((qOf w.1 : ℕ) : X.E) = Loc.n1Arg r₁ := by
      field_simp
    have p1 := hpsi _ hia
    have p2 := hpsi' _ hia
    rw [ea] at p1 p2
    rw [p1, p2]
    congr 1

    rw [lamRow_tup Ch mu mu' j hP]
    have ht : h'⁻¹ * (r⁻¹ * r₁ * r) * h'⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁'.2
    rw [inv_inv] at ht
    have e : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ) = κ⁻¹ * (h'⁻¹ * (r⁻¹ * r₁ * r) * h') * κ := by group
    rw [e]
    generalize h'⁻¹ * (r⁻¹ * r₁ * r) * h' = t at ht ⊢
    have LM := GlobalTheory.SymLevelMul.lamRow_mul Ch mu' j w.1 hjm hP
    have hκi : κ⁻¹ ∈ Jat (Pr := Pr) (R := R) true j w.1 := inv_mem hκ
    rw [LM _ (mul_mem hκi ht) _ hκ, LM _ hκi _ ht]
    have e3 : lamRow Ch mu' true j w.1 t.toLinearMap =
        lamRow Ch mu' true j w.1 t.toLinearMap * lamRow Ch mu' true j w.1 (κ⁻¹ : AutY X R j).toLinearMap *
          lamRow Ch mu' true j w.1 κ.toLinearMap := by
      conv_lhs => rw [show t = t * κ⁻¹ * κ by group]
      rw [LM _ (mul_mem ht hκi) _ hκ, LM _ ht _ hκi]
    linear_combination -e3

end GlobalTheory.Mem.Col2.IdxEx.LocMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeBidual
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelHecke.DualConj

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J L ↔ ∀ x ∈ L, hform σ J x y ∈ (algebraMap (𝓞 E) E).range := by
  have := bwG_span_dualSet σ J L
  change y ∈ ((Submodule.span (𝓞 E) (dualSet σ J L) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ↔ _
  rw [this]; rfl

omit [NumberField E] in
theorem hform_eq (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_unitary (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E)
    (hg : cT σ g * J * g = J) (x y : Fin n → E) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have e : (fun i => σ ((g *ᵥ x) i)) = (fun i => σ (x i)) ᵥ* cT σ g := by
    funext i
    simp [cT, mulVec, vecMul, dotProduct, mul_comm]
  rw [hform_eq, hform_eq, e, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

omit [NumberField E] in
theorem hform_smul_left (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J (a • x) y = σ a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

@[reducible] def starOf (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) : StarRing E where
  star := σ
  star_involutive := hσ
  star_mul a b := by rw [map_mul, mul_comm]
  star_add := map_add σ

theorem dual_lattice_bidual (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit J.det) (hH : cT σ J = J) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice E (dualL σ J L) ∧ dualL σ J (dualL σ J L) = L := by
  letI : StarRing E := starOf σ hσ
  let h : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
    LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (hform σ J)
      (fun x x' y => by simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
      (fun a x y => hform_smul_left σ J a x y)
      (fun x y y' => by simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
      (fun a x y => hform_smul_right σ J a x y)
  have hh : ∀ x y, h x y = hform σ J x y := fun _ _ => rfl
  have hsym' : ∀ x y, σ (hform σ J x y) = hform σ J y x := by
    intro x y
    have e : ∀ i j, σ (J i j) = J j i := fun i j => congrFun (congrFun hH j) i
    simp only [hform, map_sum, map_mul, hσ, e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsym : h.IsSymm := ⟨fun x y => hsym' x y⟩
  have hr : ∀ y, (∀ x, hform σ J x y = 0) → y = 0 := by
    intro y hy
    have h1 : J *ᵥ y = 0 := by
      funext i
      have := hy (Pi.single i 1)
      rw [hform_eq, dotProduct, Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hb
        simp [hb]
      · simp
    have ey : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    rw [ey, h1, mulVec_zero]
  have hnd : h.Nondegenerate := by
    refine ⟨fun x hx => hr x fun y => ?_, fun y hy => hr y hy⟩
    rw [← hsym', ← hh, hx y, map_zero]
  have hd : ∀ M : Submodule (𝓞 E) (Fin n → E), Formalism.HermitianLatticesTheory.dual h M = dualL σ J M := by
    intro M
    ext y
    rw [mem_dualL]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]
    rfl
  have := Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E (Fin n → E) h hsym hnd (fun r => LocB.sig_int σ r) L hL
  rw [hd, hd] at this
  exact ⟨this.1, this.2.1⟩

theorem localization_dualL_le (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hPQ : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P) (M N : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG)
    (h : Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N) :
    Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N) ≤ Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) := by
  have h1P : (1 : 𝓞 E) ∉ P := P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  have key : ∃ s : 𝓞 E, s ∉ P ∧ ∀ x ∈ M, s • x ∈ N := by
    have h0 : M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := fun x hx =>
      h ((rlv_mem_locP P M x).2 ⟨1, h1P, by rwa [one_smul]⟩)
    clear h
    induction M, hM using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨s, hs, hx⟩ := (rlv_mem_locP P N x).1 (h0 (Submodule.mem_span_singleton_self x))
      refine ⟨s, hs, fun y hy => ?_⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [smul_comm]; exact N.smul_mem a hx
    | sup A B _ _ hA hB =>
      obtain ⟨s, hs, h1⟩ := hA (le_sup_left.trans h0)
      obtain ⟨t, ht, h2⟩ := hB (le_sup_right.trans h0)
      refine ⟨s * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs ht, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [smul_add]
      refine N.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (h1 a ha)
      · rw [mul_smul]; exact N.smul_mem _ (h2 b hb)
  obtain ⟨s, hs, hsM⟩ := key
  obtain ⟨s', hs'⟩ := LocB.sig_int σ s
  have hs'Q : s' ∉ Q := fun hq => hs (hPQ s' s hs' hq)
  intro y hy
  obtain ⟨t, ht, hty⟩ := (rlv_mem_locP Q _ y).1 hy
  refine (rlv_mem_locP Q _ y).2 ⟨s' * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs'Q ht, ?_⟩
  rw [mem_dualL] at hty ⊢
  intro x hx
  have := hty _ (hsM x hx)
  rw [← algebraMap_smul E s x, hform_smul_left] at this
  rw [mul_smul, ← algebraMap_smul E s' (t • y), hform_smul_right, hs']
  exact this

theorem mem_mulLat (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ mulLat γ.1 L ↔ (γ⁻¹).1 *ᵥ y ∈ L := by
  rw [← map_glE, Submodule.mem_map_equiv, glE_symm_apply]

theorem mulLat_lattice (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice E (mulLat γ.1 L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : (mulLat γ.1 L : Set (Fin n → E)) = (Matrix.mulVecLin γ.1) '' (L : Set (Fin n → E)) := rfl
  rw [e, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (glE γ).surjective

theorem dualL_mulLat (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E) (hγ : γ ∈ UJ σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) : dualL σ J (mulLat γ.1 L) = mulLat γ.1 (dualL σ J L) := by
  ext y
  have ey : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ y) = y := (glE γ).apply_symm_apply y
  rw [mem_mulLat, mem_dualL, mem_dualL]
  constructor
  · intro h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    have := h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey] at this
    exact this

theorem dual_conj_primes : ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime], (∀ x, σ (σ x) = x) → IsUnit J.det → cT σ J = J → (∀ a b : 𝓞 E, (b : E) = σ (a : E) → (a ∈ Q ↔ b ∈ P)) → ∀ M N : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E M → Submodule.IsLattice E N → (Formalism.HermitianLatticesTheory.localization₂ P M = Formalism.HermitianLatticesTheory.localization₂ P N → Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N)) ∧ (Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J N) → Formalism.HermitianLatticesTheory.localization₂ Q M = Formalism.HermitianLatticesTheory.localization₂ Q N) ∧ ∀ γ : GL (Fin n) E, γ ∈ UJ σ J → Submodule.IsLattice E (mulLat γ.1 M) ∧ dualL σ J (mulLat γ.1 M) = mulLat γ.1 (dualL σ J M) := by
  intro E _ _ σ n J P Q _ _ hσ hJ hH hPQ M N hM hN
  have hPQ' : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P := fun a b hab =>
    (hPQ a b (by rw [hab, hσ])).1
  have one : ∀ A B : Submodule (𝓞 E) (Fin n → E), A.FG → B.FG → Formalism.HermitianLatticesTheory.localization₂ P A = Formalism.HermitianLatticesTheory.localization₂ P B →
      Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J A) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J B) := fun A B hA hB h =>
    le_antisymm (localization_dualL_le σ J P Q hPQ' B A hB h.ge) (localization_dualL_le σ J P Q hPQ' A B hA h.le)
  obtain ⟨hM1, hM2⟩ := dual_lattice_bidual σ hσ J hJ hH M hM
  obtain ⟨hN1, hN2⟩ := dual_lattice_bidual σ hσ J hJ hH N hN
  refine ⟨one M N hM.fg hN.fg, fun h => ?_, fun γ hγ => ⟨mulLat_lattice γ M hM, dualL_mulLat σ J γ hγ M⟩⟩
  have := one _ _ hM1.fg hN1.fg h
  rwa [hM2, hN2] at this

end GlobalTheory.LevelHecke.DualConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolInfIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bijective_fam (σ : E →ₐ[F] E) {I : Type} (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ))
    (h : IsCMExt F E σ) (hτ : IsCMFam τ) (hθ : ∀ i, IsInfEmb (τ i) (θ i)) :
    Function.Bijective (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ : E →+* ℂ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := by
    intro φ
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by
        show InfinitePlace.mk (τ j) = InfinitePlace.mk (τ i)
        rw [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · refine absurd ⟨i, ?_⟩ hn
        rw [← e]
        ext x
        simp
  have hb := GlobalTheory.InfAdeleCM.bijective c h2 hc hc' θ0
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)) (Set.range τ) hΨ
  have hinj : Function.Injective τ := fun i j hij => hτ.1 (by
    show InfinitePlace.mk (τ i) = InfinitePlace.mk (τ j)
    rw [hij])
  let u : I ≃ Set.range τ := Equiv.ofInjective τ hinj
  have he : (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) =
      (Equiv.arrowCongr u.symm (Equiv.refl ℂ)) ∘ (fun (z : Ainf F ⊗[F] E) (φ : Set.range τ) => θ0 φ.1 z) := by
    funext z i
    rw [GlobalTheory.Mem.VolEmb.infEmb_unique (τ i) (θ i) (θ0 (τ i)) (hθ i) ⟨h0 _, h0' _⟩]
    rfl
  rw [he]
  exact (Equiv.bijective _).comp hb

theorem infEmb_sigR (σ : E →ₐ[F] E) (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (h : IsCMExt F E σ) (hθ : IsInfEmb τ θ) (z : Ainf F ⊗[F] E) :
    θ (sigR (Ainf F) σ z) = star (θ z) := by
  obtain ⟨hF, -, -, hσ⟩ := h
  have hθ' := GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show θ (a ⊗ₜ[F] σ x) = starRingEnd ℂ _
    rw [hθ', hθ', map_mul, GlobalTheory.InfAdeleCM.conj_ext, hσ]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, star_add]

theorem exists_infAdele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → ∃ e : (Ainf F ⊗[F] E) ≃+* (I → ℂ), (∀ x i, e x i = θ i x) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x i, e (sigR (Ainf F) σ x) i = star (e x i) := by
  intro F E _ _ _ _ _ σ I _ τ θ h hτ hθ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e0.secondCountableTopology
  have hb : Function.Bijective (Pi.ringHom θ : Ainf F ⊗[F] E →+* (I → ℂ)) := bijective_fam σ τ θ h hτ hθ
  let e : (Ainf F ⊗[F] E) ≃+* (I → ℂ) := RingEquiv.ofBijective _ hb
  have hc : Continuous e := continuous_pi fun i =>
    IsModuleTopology.continuous_of_ringHom (R := Ainf F) (θ i) (hθ i).2
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective hc
  refine ⟨e, fun _ _ => rfl, hc, ?_, fun x i => infEmb_sigR σ (τ i) (θ i) h (hθ i) x⟩
  exact (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous

end GlobalTheory.Mem.VolInfIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNhdsOneUnitaryGroupRationalPointEqOne
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_nhds_one_rational_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ U ∈ nhds (1 : HA (AF F) σ J), ∀ g ∈ U, (∃ γ : HFinIn (AF F) σ J, γ • (1 : HA (AF F) σ J) = g) → g = 1 := by
  intro F E _ _ _ _ _ σ M J
  have hd := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have h1 : ({1} : Set (HFinIn (AF F) σ J)) ∈ nhds (1 : HFinIn (AF F) σ J) :=
    (isOpen_discrete _).mem_nhds rfl
  obtain ⟨U, hU, hsub⟩ := (mem_nhds_subtype _ _ _).1 h1
  refine ⟨U, hU, ?_⟩
  rintro g hg ⟨γ, rfl⟩
  have hγ : γ • (1 : HA (AF F) σ J) = (γ.1 : HR (AF F) σ J) := mul_one (γ.1 : HR (AF F) σ J)
  rw [hγ] at hg ⊢
  have h2 : γ = 1 := hsub hg
  rw [h2]
  rfl

end GlobalTheory.Mem.Vol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_generate_ideal_projective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ J : X.IdealSheafData, ∃ (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec), Generates J σ := by
  first | exact @GlobalTheory.ProjBlowup.exists_generates | exact GlobalTheory.ProjBlowup.exists_generates | (intros; apply GlobalTheory.ProjBlowup.exists_generates <;> assumption)
end

