import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def bor (a d : kˣ) (x : k) : GL (Fin (1 + 1)) k :=
  GeneralLinearGroup.mkOfDetNeZero !![(a : k), x; 0, (d : k)] (by simp)

def nU (x : k) : GL (Fin (1 + 1)) k := bor 1 1 x

def nL (x : k) : GL (Fin (1 + 1)) k := GeneralLinearGroup.mkOfDetNeZero !![1, 0; x, 1] (by simp)

def wE : GL (Fin (1 + 1)) k := GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp)

def tD (a d : kˣ) : GL (Fin (1 + 1)) k := bor a d 0

@[simp] theorem val_bor (a d : kˣ) (x : k) :
    ((bor a d x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![(a : k), x; 0, (d : k)] := rfl

@[simp] theorem val_nL (x : k) :
    ((nL x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![1, 0; x, 1] := rfl

@[simp] theorem val_wE :
    ((wE : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![0, 1; 1, 0] := rfl

@[simp] theorem val_nU (x : k) :
    ((nU x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![1, x; 0, 1] := by
  simp [nU]

@[simp] theorem val_tD (a d : kˣ) :
    ((tD a d : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![(a : k), 0; 0, (d : k)] := by
  simp [tD]

theorem nU_mul_nU (x y : k) : (nU x : GL (Fin (1 + 1)) k) * nU y = nU (x + y) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem wE_mul_wE : (wE : GL (Fin (1 + 1)) k) * wE = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem nL_eq (x : k) : (nL x : GL (Fin (1 + 1)) k) = wE * nU x * wE := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wE_mul_nU_eq (x : kˣ) :
    (wE : GL (Fin (1 + 1)) k) * nU (x : k) = bor (-x⁻¹) x 1 * nL ((x⁻¹ : kˣ) : k) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wE_mul_nU_mul_tD (x : k) (a d : kˣ) :
    (wE : GL (Fin (1 + 1)) k) * nU x * tD a d = tD d a * wE * nU (x * d * ((a⁻¹ : kˣ) : k)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem tD_inv_eq (a : kˣ) : (tD a a⁻¹ : GL (Fin (1 + 1)) k) =
    nU (a : k) * nL (-((a⁻¹ : kˣ) : k)) * nU (a : k) * (nU (-1) * nL 1 * nU (-1)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

abbrev PSp (μ₁ μ₂ : kˣ →* ℂˣ) : Type :=
  IndSp (two (stdSum (rfl : 1 + 1 = 1 + 1)))
    ((extTensor (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)).comp (leviTwo k (Fin 1) (Fin 1)).symm.toMonoidHom)

abbrev psRep (μ₁ μ₂ : kˣ →* ℂˣ) : Representation ℂ (GL (Fin (1 + 1)) k) (PSp μ₁ μ₂) :=
  prod₂ (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)

def ev {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) : ℂ := TensorProduct.lid ℂ ℂ (f.1.1 g)

def coord {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (x : k) : ℂ := ev f (wE * nU x)

def bchar (μ₁ μ₂ : kˣ →* ℂˣ) (a d : kˣ) : ℂ :=
  ((μ₁ a * μ₂ d * absPow k (1 / 2) a * absPow k (-1 / 2) d : ℂˣ) : ℂ)

theorem ev_add {μ₁ μ₂ : kˣ →* ℂˣ} (f f' : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (f + f') g = ev f g + ev f' g := by
  show TensorProduct.lid ℂ ℂ (f.1.1 g + f'.1.1 g) = _
  rw [map_add]; rfl

theorem ev_smul {μ₁ μ₂ : kˣ →* ℂˣ} (c : ℂ) (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (c • f) g = c * ev f g := by
  show TensorProduct.lid ℂ ℂ (c • f.1.1 g) = _
  rw [map_smul]; rfl

theorem ev_sub {μ₁ μ₂ : kˣ →* ℂˣ} (f f' : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (f - f') g = ev f g - ev f' g := by
  show TensorProduct.lid ℂ ℂ (f.1.1 g - f'.1.1 g) = _
  rw [map_sub]; rfl

theorem ev_act {μ₁ μ₂ : kˣ →* ℂˣ} (h : GL (Fin (1 + 1)) k) (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (psRep μ₁ μ₂ h f) g = ev f (g * h) := rfl

theorem ext_ev {μ₁ μ₂ : kˣ →* ℂˣ} {f f' : PSp μ₁ μ₂} (h : ∀ g, ev f g = ev f' g) : f = f' := by
  apply Subtype.ext; apply Subtype.ext; funext g
  exact (TensorProduct.lid ℂ ℂ).injective (h g)

theorem bor_mem_parab (a d : kˣ) (x : k) :
    bor a d x ∈ parab k (two (stdSum (rfl : 1 + 1 = 1 + 1))) := by
  refine mem_parab_iff.2 fun b c i j hbc => ?_
  cases b <;> cases c
  · exact absurd hbc (by decide)
  · exact absurd hbc (by decide)
  swap
  · exact absurd hbc (by decide)
  show (bor a d x : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨true, i⟩)
    ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨false, j⟩) = 0
  rw [two_true, two_false, Subsingleton.elim i 0, Subsingleton.elim j 0]
  have h1 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inr (0 : Fin 1)) = 1 := by decide
  have h0 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inl (0 : Fin 1)) = 0 := by decide
  rw [h1, h0, val_bor]
  rfl

theorem ev_bor {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (a d : kˣ) (x : k) (g : GL (Fin (1 + 1)) k) :
    ev f (bor a d x * g) = bchar μ₁ μ₂ a d * ev f g := by
  have h := f.1.2 ⟨_, bor_mem_parab a d x⟩ g
  simp only [ev]
  rw [show (bor a d x * g) = ((⟨_, bor_mem_parab a d x⟩ : parab k _) : GL (Fin (1 + 1)) k) * g from rfl, h]
  generalize f.1.1 g = v
  set p : parab k (two (stdSum (rfl : 1 + 1 = 1 + 1))) := ⟨_, bor_mem_parab a d x⟩
  have h1 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inr (0 : Fin 1)) = 1 := by decide
  have h0 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inl (0 : Fin 1)) = 0 := by decide
  have e1 : GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : 1 + 1 = 1 + 1))) p false) = a := by
    ext
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    show (bor a d x : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨false, default⟩)
      ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨false, default⟩) = a
    rw [two_false, Subsingleton.elim (default : Fin 1) 0, h0, val_bor]
    rfl
  have e2 : GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : 1 + 1 = 1 + 1))) p true) = d := by
    ext
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    show (bor a d x : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨true, default⟩)
      ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨true, default⟩) = d
    rw [two_true, Subsingleton.elim (default : Fin 1) 0, h1, val_bor]
    rfl
  have hd : (deltaHalf k (Two (Fin 1) (Fin 1)) (leviProj k (two (stdSum (rfl : 1 + 1 = 1 + 1))) p) : ℂ) =
      ((absPow k (1 / 2) a * absPow k (-1 / 2) d : ℂˣ) : ℂ) := by
    rw [← MulEquiv.apply_symm_apply (leviTwo k (Fin 1) (Fin 1)) (leviProj k _ p), deltaHalf_two]
    simp only [Fintype.card_fin, Nat.cast_one]
    rw [show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).1 = leviProj k _ p false from rfl,
      show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).2 = leviProj k _ p true from rfl, e1, e2]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul y z =>
    show TensorProduct.lid ℂ ℂ ((deltaHalf k _ (leviProj k _ p) : ℂ) • extTensor (detRep (Fin 1) μ₁)
      (detRep (Fin 1) μ₂) ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)) (y ⊗ₜ z)) = _
    rw [extTensor_tmul, hd]
    rw [show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).1 = leviProj k _ p false from rfl,
      show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).2 = leviProj k _ p true from rfl]
    simp only [detRep, ofChar_apply, detChar_apply, e1, e2, map_smul, TensorProduct.lid_tmul, bchar,
      Units.val_mul, smul_eq_mul]
    ring
  | add y z hy hz =>
    rw [map_add, map_add, map_add, hy, hz, mul_add]

def evL (μ₁ μ₂ : kˣ →* ℂˣ) (g : GL (Fin (1 + 1)) k) : PSp μ₁ μ₂ →ₗ[ℂ] ℂ where
  toFun f := ev f g
  map_add' f f' := ev_add f f' g
  map_smul' c f := ev_smul c f g

def coordL (μ₁ μ₂ : kˣ →* ℂˣ) : PSp μ₁ μ₂ →ₗ[ℂ] (k → ℂ) where
  toFun f := coord f
  map_add' f f' := funext fun x => ev_add f f' _
  map_smul' c f := funext fun x => ev_smul c f _

@[simp] theorem evL_apply (μ₁ μ₂ : kˣ →* ℂˣ) (g : GL (Fin (1 + 1)) k) (f : PSp μ₁ μ₂) :
    evL μ₁ μ₂ g f = ev f g := rfl

@[simp] theorem coordL_apply (μ₁ μ₂ : kˣ →* ℂˣ) (f : PSp μ₁ μ₂) : coordL μ₁ μ₂ f = coord f := rfl

theorem coord_nU {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (y x : k) :
    coord (psRep μ₁ μ₂ (nU y) f) x = coord f (x + y) := by
  simp only [coord, ev_act, mul_assoc, nU_mul_nU]

theorem coord_tD {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (a d : kˣ) (x : k) :
    coord (psRep μ₁ μ₂ (tD a d) f) x = bchar μ₁ μ₂ d a * coord f (x * d * ((a⁻¹ : kˣ) : k)) := by
  simp only [coord, ev_act]
  rw [wE_mul_nU_mul_tD, tD, mul_assoc, mul_assoc, ev_bor, ← mul_assoc]

theorem bchar_ne_zero (μ₁ μ₂ : kˣ →* ℂˣ) (a d : kˣ) : bchar μ₁ μ₂ a d ≠ 0 := Units.ne_zero _

@[simp] theorem bchar_one (μ₁ μ₂ : kˣ →* ℂˣ) : bchar μ₁ μ₂ 1 1 = 1 := by simp [bchar]

theorem ev_act_bor_one {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (a d : kˣ) (x : k) :
    ev (psRep μ₁ μ₂ (bor a d x) f) 1 = bchar μ₁ μ₂ a d * ev f 1 := by
  rw [ev_act, one_mul, ← mul_one (bor a d x), ev_bor]

def ball (c : k) (r : kˣ) : Set k := {z | valuation k (z - c) ≤ valuation k (r : k)}

def elemDiff (c c' : k) (r : kˣ) : k → ℂ := (ball c r).indicator 1 - (ball c' r).indicator 1

variable (k) in

def elemSpan : Submodule ℂ (k → ℂ) :=
  Submodule.span ℂ (Set.range fun p : k × k × kˣ => elemDiff p.1 p.2.1 p.2.2)

def IsLC (Φ : k → ℂ) : Prop := ∃ r : kˣ, ∀ x y : k, valuation k y ≤ valuation k (r : k) → Φ (x + y) = Φ x

def IsCS (Φ : k → ℂ) : Prop := ∃ R : kˣ, ∀ x : k, valuation k (R : k) < valuation k x → Φ x = 0

def IsEvRad (Φ : k → ℂ) : Prop :=
  ∃ R : kˣ, ∀ x y : k, valuation k (R : k) < valuation k x → valuation k x = valuation k y → Φ x = Φ y

end GlobalTheory.PrinTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
section
noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}

theorem invariant_comp_mulVec [Fintype κ] [DecidableEq κ] (m : ((κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ SB (κ → F), ∀ a, m (fun x => φ (x + a)) = m φ) (g : GL κ F) {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F))
    (hφ' : (fun x => φ (g.val.mulVec x)) ∈ SB (κ → F)) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * m (fun x => φ (g.val.mulVec x)) = m φ := by
  borelize F
  have := SplitWeil.secondCountable F
  have := SplitWeil.t2Space F
  have := nonarch_pi F κ
  obtain ⟨c, hc⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → F) (Measure.pi fun _ => (Measure.addHaar : Measure F)) m hm
  rw [hc _ hφ, hc _ hφ', mul_left_comm, integral_comp_mulVec]

theorem diag_mem_SB [Fintype κ] {φ : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) :
    (fun x : κ → F => φ (Sum.elim x x)) ∈ SB (κ → F) := by
  have := SplitWeil.t2Space F
  have hc : Continuous fun x : κ → F => (Sum.elim x x : κ ⊕ κ → F) :=
    continuous_pi (by rintro (k | k) <;> exact continuous_apply k)
  have hc' : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  refine ⟨hφ.1.comp_continuous hc, HasCompactSupport.intro (hφ.2.image hc') fun x hx => ?_⟩
  by_contra h
  exact hx ⟨Sum.elim x x, subset_tsupport _ h, rfl⟩

theorem diag_invariant_comp [Invertible (2 : F)] [Fintype κ] [DecidableEq κ] (ψ : AddChar F ℂ) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (l : ((κ ⊕ κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ x y : κ → F, ∀ φ ∈ SB (κ ⊕ κ → F), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ)
    (g : GL κ F) {φ φ' : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) (hφ' : φ' ∈ SB (κ ⊕ κ → F))
    (h : ∀ x, φ' (Sum.elim x x) = φ (Sum.elim (g.val.mulVec x) (g.val.mulVec x))) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * l φ' = l φ := by
  classical
  have := SplitWeil.t2Space F
  have := nonarch_field F
  have hlc := isLocallyConstant_addChar ψ hψ

  have hz : ∀ φ ∈ SB (κ ⊕ κ → F), (∀ x, φ (Sum.elim x x) = 0) → l φ = 0 := by
    intro φ hφ h0
    refine eq_zero_of_mul_invariant l (Set.range fun y : κ → F => fun u => ψ (u ⬝ᵥ Sum.elim y (-y))) ?_ ?_ hφ ?_
    · rintro _ ⟨y, rfl⟩
      exact hlc.comp_continuous (continuous_id.dotProduct continuous_const)
    · rintro _ ⟨y, rfl⟩ φ hφ
      rw [← hl 0 y φ hφ]
      congr 1
      funext u
      simp [schr]
    · intro u hu
      obtain ⟨k, hk⟩ : ∃ k, u (Sum.inl k) - u (Sum.inr k) ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hu
        rw [← h0 (u ∘ Sum.inl)]
        congr 1
        ext (k | k)
        · rfl
        · exact (sub_eq_zero.mp (hne k)).symm
      obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ1
      refine ⟨_, ⟨Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))), rfl⟩, ?_⟩
      have : u ⬝ᵥ Sum.elim (Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))))
          (-Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k)))) = a := by
        conv_lhs => rw [← Sum.elim_comp_inl_inr u]
        rw [sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_single, dotProduct_single, ← sub_eq_add_neg,
          ← sub_mul]
        exact mul_div_cancel₀ _ hk
      show ψ _ ≠ 1
      rwa [this]

  let K : Set (κ → F) := Set.univ.pi fun _ => (𝒪[F] : Set F)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => SplitWeil.isCompact_int F
  have hK : IsClopen K := ⟨hKc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => SplitWeil.isOpen_int F⟩
  let e : (κ → F) → ℂ := K.indicator 1
  have he : IsLocallyConstant e := (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant
  have he0 : e 0 = 1 := Set.indicator_of_mem (show (0 : κ → F) ∈ K from fun _ _ => zero_mem _) _
  let ext : ((κ → F) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → F) → ℂ) :=
    { toFun := fun f u => f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl)
      map_add' := fun f f' => by funext u; simp [add_mul]
      map_smul' := fun a f => by funext u; simp [mul_assoc] }
  have hext : ∀ f u, ext f u = f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl) := fun _ _ => rfl
  have c1 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  have c2 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inr := continuous_pi fun k => continuous_apply _
  have hSB : ∀ f ∈ SB (κ → F), ext f ∈ SB (κ ⊕ κ → F) := by
    intro f hf
    have c3 : Continuous fun p : (κ → F) × (κ → F) => (Sum.elim p.1 (p.2 + p.1) : κ ⊕ κ → F) :=
      continuous_pi (by rintro (k | k) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> fun_prop)
    refine ⟨(hf.1.comp_continuous c1).mul (he.comp_continuous (c2.sub c1)),
      HasCompactSupport.intro ((IsCompact.prod hf.2 hKc).image c3) fun u hu => ?_⟩
    by_contra h
    rw [hext] at h
    refine hu ⟨(u ∘ Sum.inl, u ∘ Sum.inr - u ∘ Sum.inl),
      ⟨subset_tsupport _ (left_ne_zero_of_mul h), Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩, ?_⟩
    simp
  have hres : ∀ φ ∈ SB (κ ⊕ κ → F), l φ = (l ∘ₗ ext) fun x => φ (Sum.elim x x) := by
    intro φ hφ
    rw [LinearMap.comp_apply, ← sub_eq_zero, ← map_sub]
    refine hz _ (sub_mem hφ (hSB _ (diag_mem_SB hφ))) fun x => ?_
    simp [hext, he0]
  have hinv : ∀ f ∈ SB (κ → F), ∀ a, (l ∘ₗ ext) (fun x => f (x + a)) = (l ∘ₗ ext) f := by
    intro f hf a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hl a 0 _ (hSB f hf)]
    congr 1
    funext u
    have e1 : (u + Sum.elim a a) ∘ Sum.inl = u ∘ Sum.inl + a := rfl
    have e2 : (u + Sum.elim a a) ∘ Sum.inr = u ∘ Sum.inr + a := rfl
    simp [schr, hext, e1, e2]
  have h' := diag_mem_SB hφ'
  rw [hres φ hφ, hres φ' hφ']
  simp only [h] at h' ⊢
  exact invariant_comp_mulVec _ hinv g (diag_mem_SB hφ) h'

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]

theorem siegelRule_split (ψ : AddChar F ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {JA : Matrix α α (F × F)}
    {JB : Matrix β β (F × F)} (hA : IsHerm (swapA F) JA) (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β)
    (χ : (F × F)ˣ →* Circle) (hχ : ∀ a : Fˣ, χ (Units.map (algebraMap F (F × F) : F →* F × F) a) = 1) :
    SiegelRule (swapA F) (sbClass F) ψ (1, -1) JA (dbl JB) (splitDarboux hA hB.dbl (dblNum σ)) χ (diagCols β)
      (splitOm (distribHaarChar F) χ (dbl JB) (dblNum σ)) := by
  classical
  intro l _ hl p t hp φ hφ
  have hD : ∀ {S : Type} [CommRing S] (z : Matrix α β S), z * (diagCols β : Matrix (β ⊕ β) β S)ᵀ = fromCols z z := by
    intro S _ z
    rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one]
  have hl' : ∀ x y : κ → F, ∀ φ ∈ SB (κ ⊕ κ → F), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ := by
    intro x y φ hφ
    have := hl ((splitDarboux hA hB σ).e.symm (x, y)) φ hφ
    rwa [Darboux.rho, hD, isDblCoord_split hA hB σ, LinearEquiv.apply_symm_apply] at this
  obtain ⟨h1, h2⟩ := det_siegel hB p t.val hp
  let t₁ : GL β F := GeneralLinearGroup.map (RingHom.fst F F) t
  let t₂ : GL β F := GeneralLinearGroup.map (RingHom.snd F F) t
  have h2' : GeneralLinearGroup.det (ugFst _ p) = GeneralLinearGroup.det t₁ * (GeneralLinearGroup.det t₂)⁻¹ :=
    eq_mul_inv_of_mul_eq (Units.ext h2)
  have h1' : ((ugFst _ p)⁻¹).val * (diagCols β : Matrix (β ⊕ β) β F) =
      (diagCols β : Matrix (β ⊕ β) β F) * (t₁⁻¹).val := by
    have h3 : (ugFst _ p).val * (diagCols β : Matrix (β ⊕ β) β F) = (diagCols β : Matrix (β ⊕ β) β F) * t₁.val := h1
    have := congrArg (fun N => ((ugFst _ p)⁻¹).val * N * (t₁⁻¹).val) h3
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let G : Matrix κ κ F := ((1 : Matrix α α F) ⊗ₖ (t₁⁻¹).val).submatrix σ σ
  have hG : G.det = ((GeneralLinearGroup.det t₁)⁻¹ ^ Fintype.card α : Fˣ) := by
    rw [det_submatrix_equiv_self, det_kronecker, det_one, one_pow, one_mul, ← map_inv, Units.val_pow_eq_pow_val]
    rfl
  let g : GL κ F := GeneralLinearGroup.mkOfDetNeZero G (hG ▸ Units.ne_zero _)
  have hg : GeneralLinearGroup.det g = (GeneralLinearGroup.det t₁)⁻¹ ^ Fintype.card α := Units.ext hG
  have hgx : ∀ X : Matrix α β F, g.val.mulVec (flat σ X) = flat σ (X * (t₁⁻¹).valᵀ) := by
    intro X
    funext k
    show ∑ k', ((1 : Matrix α α F) ⊗ₖ (t₁⁻¹).val) (σ k) (σ k') * X (σ k').1 (σ k').2 = _
    rw [Fintype.sum_equiv σ _ (fun q => ((1 : Matrix α α F) ⊗ₖ (t₁⁻¹).val) (σ k) q * X q.1 q.2) fun _ => rfl,
      Fintype.sum_prod_type, flat_apply, mul_apply]
    simp [kroneckerMap_apply, one_apply, mul_comm]
  set s := splitChar (distribHaarChar F) χ (Fintype.card α) (GeneralLinearGroup.det (ugFst _ p)) with hs
  have key := diag_invariant_comp ψ hψ hψ1 l hl' g ((SB _).smul_mem s hφ)
    (splitOm_mem_SB (distribHaarChar F) χ (dbl JB) (dblNum σ) p hφ) (fun x => by
      obtain ⟨X, rfl⟩ := (flat σ).surjective x
      rw [splitOm_apply, hgx, ← flat_fromCols, ← flat_fromCols, LinearEquiv.symm_apply_apply, ← hD, ← hD,
        Matrix.mul_assoc, Matrix.mul_assoc, ← transpose_mul, ← transpose_mul, h1']
      rfl)
  have hpos : ∀ u : Fˣ, (0 : ℝ) < distribHaarChar F u := fun u => distribHaarChar_pos (A := F) (g := u)
  have hne : ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  refine mul_left_cancel₀ hne ?_
  rw [key, map_smul, smul_eq_mul, ← mul_assoc]
  congr 1
  have hdet : GeneralLinearGroup.det t = Units.map (MonoidHom.inl F F) (GeneralLinearGroup.det (ugFst _ p)) *
      Units.map (algebraMap F (F × F) : F →* F × F) (GeneralLinearGroup.det t₂) := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact ((RingHom.fst F F).map_det t.val).trans h2.symm
    · exact ((RingHom.snd F F).map_det t.val).trans (one_mul _).symm
  have hN : Units.map (Algebra.norm F : F × F →* F) (GeneralLinearGroup.det t) =
      GeneralLinearGroup.det t₁ * GeneralLinearGroup.det t₂ := by
    refine Units.ext ((norm_pair _).trans ?_)
    exact congrArg₂ (· * ·) ((RingHom.fst F F).map_det t.val) ((RingHom.snd F F).map_det t.val)
  rw [hN, hdet, map_mul χ, hχ, mul_one, hs, mul_left_comm]
  refine congrArg₂ (fun x y : ℂ => x * y) rfl ?_
  show ((_ : ℝ) : ℂ) = _ * (((distribHaarChar F _ : ℝ) ^ _ : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, hg, h2']
  congr 1
  simp only [map_mul, map_pow, map_inv, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv]
  have p1 := hpos (GeneralLinearGroup.det t₁)
  have p2 := hpos (GeneralLinearGroup.det t₂)
  generalize (distribHaarChar F (GeneralLinearGroup.det t₁) : ℝ) = a at p1
  generalize (distribHaarChar F (GeneralLinearGroup.det t₂) : ℝ) = b at p2
  rw [Real.mul_rpow p1.le (inv_pos.mpr p2).le, Real.mul_rpow p1.le p2.le, Real.inv_rpow p2.le, ← Real.rpow_neg p2.le,
    inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg p1.le, ← mul_assoc, ← Real.rpow_add p1]
  congr 2 <;> ring

section Pair

variable {R : Type} [CommRing R]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] in
theorem flat_transpose (σ : κ ≃ α × β) (X : Matrix α β R) : flat (σ.trans (Equiv.prodComm α β)) Xᵀ = flat σ X := rfl

omit [DecidableEq β] [Fintype κ] in
theorem splitOm_swap_apply (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (J : Matrix α α (R × R)) (σ : κ ≃ α × β)
    (g : UG (swapA R) J) (φ : (κ → R) → ℂ) (X : Matrix α β R) :
    splitOm m χ J (σ.trans (Equiv.prodComm α β)) g φ (flat σ X) =
      splitChar m χ (Fintype.card β) (GeneralLinearGroup.det (ugFst J g)) * φ (flat σ (((ugFst J g)⁻¹).val * X)) := by
  rw [splitOm_apply, ← flat_transpose σ X, LinearEquiv.symm_apply_apply, ← transpose_mul, flat_transpose]

def splitPair (m : Rˣ →* ℝ≥0) (χA χB : (R × R)ˣ →* Circle) (JA : Matrix α α (R × R)) (JB : Matrix β β (R × R))
    (σ : κ ≃ α × β) : UG (swapA R) JA × UG (swapA R) JB →* Module.End ℂ ((κ → R) → ℂ) :=
  (splitOm m χB JA (σ.trans (Equiv.prodComm α β))).noncommCoprod (splitOm m χA JB σ) fun g h => by
    refine LinearMap.ext fun φ => funext fun u => ?_
    obtain ⟨X, rfl⟩ := (flat σ).surjective u
    rw [Module.End.mul_apply, Module.End.mul_apply, splitOm_swap_apply, splitOm_apply, splitOm_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, splitOm_swap_apply, Matrix.mul_assoc, mul_left_comm]

theorem resEtaPow_split_iff (χ : (R × R)ˣ →* Circle) (n : ℕ) :
    ResEtaPow (⊥ : Subgroup Rˣ) χ n ↔ ∀ a : Rˣ, χ (Units.map (algebraMap R (R × R) : R →* R × R) a) = 1 := by
  refine forall_congr' fun a => ?_
  have : a ∈ (⊥ : Subgroup Rˣ) ⊔ (Units.map (Algebra.norm R : R × R →* R)).range :=
    Subgroup.mem_sup_right ⟨Units.map (MonoidHom.inl R R) a, Units.ext ((norm_pair _).trans (mul_one _))⟩
  rw [if_pos this, Circle.coe_eq_one]

end Pair

end GlobalTheory.WeilM

end
end

