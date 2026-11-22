import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorScalarUniformizer
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.CellScalarTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Cell

variable {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem cellFunctor_central (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) (χ' : Levi k m → ℂˣ) (hρ : ∀ y v, ρ y v = ((χ' y : ℂˣ) : ℂ) • v)
    (x : Levi k m') (hx : x ∈ relParab k g) (hcomm : ∀ y, y * x = x * y) (w) :
    cellFunctor f g ρ x w =
      ((relDeltaHalf k (fun j i => c i j) (relProj k g ⟨x, hx⟩) *
        (relDeltaHalf k c (swapBlocks k c (relProj k g ⟨x, hx⟩)))⁻¹ *
          χ' (relEmb k f (swapBlocks k c (relProj k g ⟨x, hx⟩))) : ℂˣ) : ℂ) • w := by
  apply Subtype.ext; apply Subtype.ext; funext y
  show w.1.1 (y * x) = _
  rw [hcomm y]
  have h2 : w.1.1 (x * y) = _ := w.1.2 ⟨x, hx⟩ y
  rw [h2]
  show _ = ((relDeltaHalf k (fun j i => c i j) (relProj k g ⟨x, hx⟩) *
        (relDeltaHalf k c (swapBlocks k c (relProj k g ⟨x, hx⟩)))⁻¹ *
          χ' (relEmb k f (swapBlocks k c (relProj k g ⟨x, hx⟩))) : ℂˣ) : ℂ) • w.1.1 y
  generalize w.1.1 y = u
  induction u using Submodule.Quotient.induction_on with
  | H v =>
  rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, relJac_mk, hρ]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, smul_smul, ← Submodule.Quotient.mk_smul]
  rw [mul_assoc]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] in

theorem scalar_comm (s : β → kˣ) (x : Levi k m') (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j))
    (y : Levi k m') : y * x = x * y := by
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, hx]
  ext1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] [LinearOrder β] in

theorem scalar_mem (g : ∀ j, (Σ i, c i j) ≃ m' j) (s : β → kˣ) (x : Levi k m')
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j)) : x ∈ relParab k g := by
  intro j _
  rw [hx]
  refine mem_parab.2 fun a b hab => ?_
  have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
  simp [Matrix.GeneralLinearGroup.scalar, hne]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] [LinearOrder β] in

theorem det_relProj (g : ∀ j, (Σ i, c i j) ≃ m' j) (s : β → kˣ) (x : Levi k m')
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j)) (h : x ∈ relParab k g) (j : β) (i : α) :
    GeneralLinearGroup.det (relProj k g ⟨x, h⟩ j i) = s j ^ Fintype.card (c i j) := by
  have e : relProj k g ⟨x, h⟩ j i = GeneralLinearGroup.scalar _ (s j) := by
    ext a a'
    refine (leviProj_apply k (g j) ⟨x j, h j trivial⟩ i a a').trans ?_
    show ((x j : GL (m' j) k) : Matrix (m' j) (m' j) k) _ _ = _
    rw [hx]
    by_cases h : a = a'
    · subst h; simp [Matrix.GeneralLinearGroup.scalar]
    · have h' : g j ⟨i, a⟩ ≠ g j ⟨i, a'⟩ := by simpa using h
      simp [Matrix.GeneralLinearGroup.scalar, h, h']
  rw [e]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end Cell

theorem modExp_false (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m false = Fintype.card (m true) := by
  simp [modExp, Finset.sum_filter]

theorem modExp_true (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m true = -(Fintype.card (m false) : ℤ) := by
  simp [modExp, Finset.sum_filter]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem extTensor_detRep_apply (χ₁ χ₂ : kˣ →* ℂˣ) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (y : Levi k (Two a b)) (t : TensorProduct ℂ ℂ ℂ) :
    ((extTensor (detRep a χ₁) (detRep b χ₂)).comp (leviTwo k a b).symm.toMonoidHom) y t =
      ((χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true)) : ℂˣ) : ℂ) • t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => rw [map_add, hs, ht, smul_add]
  | tmul s t =>
    refine (extTensor_tmul (detRep a χ₁) (detRep b χ₂) (y false, y true) s t).trans ?_
    rw [detRep, detRep, ofChar_apply, ofChar_apply, ← smul_eq_mul, ← smul_eq_mul,
      TensorProduct.smul_tmul_smul]
    rfl

theorem cellFunctor_scalar_action {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))) (hb : b.1 false true = 1)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ)
    (x : Levi k (Two (Fin (u + v)) (Fin 1)))
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ ((fun j : Bool => if j then ϖ else 1) j)) (w) :
    cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
      x w =
      (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  have hm := scalar_mem (c := fun i j => Fin (b.1 i j)) g _ x hx
  have hd := det_relProj (c := fun i j => Fin (b.1 i j)) g _ x hx hm
  have h11 : b.1 true true = 0 := by
    have := b.2.2 true
    simp only [Fintype.sum_bool, Fintype.card_fin] at this
    omega
  have h00 : (b.1 false false : ℂ) = u - 1 := by
    have := b.2.1 false
    simp only [Fintype.sum_bool, Fintype.card_fin] at this
    have h3 : b.1 false false + 1 = u := by omega
    rw [eq_sub_iff_add_eq]
    exact_mod_cast h3
  refine (cellFunctor_central (c := fun i j => Fin (b.1 i j)) f g _
    (fun y => χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true)))
    (extTensor_detRep_apply χ₁ χ₂ (Fin u) (Fin (v + 1))) x hm (scalar_comm _ x hx) w).trans ?_
  refine congrArg (fun s : ℂˣ => (s : ℂ) • w) ?_
  have hd' : ∀ i j, GeneralLinearGroup.det
      (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g ⟨x, hm⟩) i j) = _ := fun i j => hd j i
  simp only [relDeltaHalf_apply, deltaHalf_apply, relEmb_apply, det_leviEmb, Fintype.prod_bool, hd, hd',
    modExp_false, modExp_true, Fintype.card_fin, hb, h11]
  have hz : absPow k (-(b.1 false false : ℂ) / 2) = (absPow k (((u : ℂ) - 1) / 2))⁻¹ := by
    rw [h00, neg_div, absPow_neg]
  simp [hz, mul_comm]

theorem cellFunctor_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))) (hb : b.1 false true = 1)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ) (w) :
    cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
      (leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) w =
      (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  have hx : ∀ j, leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) j =
      GeneralLinearGroup.scalar _ ((fun j : Bool => if j then ϖ else 1) j) := by
    intro j
    cases j
    · exact (map_one (GeneralLinearGroup.scalar (R := k) (Fin (u + v)))).symm
    · rfl
  exact cellFunctor_scalar_action χ₁ χ₂ u v b hb f g ϖ _ hx w

end GlobalTheory.CellScalarTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.Incl

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem subst_expAlong {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    {κ : Type} [Fintype κ] {ι : κ → Type} [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin d → C)
    (A : κ → Matrix (Fin d) (Fin d) C) (t : κ → C) (hA : ∀ b a, (A b).mulVec (u b a) = t b • u b a) (i : Fin d) :
    subst (expAlong (fun _ : κ => G) u)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C))) i) =
      subst (fun e : Fin d => ∑ ℓ : (Σ b, ι b), (t ℓ.1 * u ℓ.1 ℓ.2 e) • (X ℓ : MvPowerSeries (Σ b, ι b) C))
        (expOf G i) := by
  have hu : ∀ (b : κ) (e : Fin d),
      constantCoeff (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := fun b e => by simp
  have hE : ∀ (b : κ), (fun e : Fin d => expAlong (fun _ : κ => G) u ⟨b, e⟩) =
      expPt G (fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) := fun b => rfl
  have hs : HasSubst (expAlong (fun _ : κ => G) u) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hu q.1) q.2
  have hX : ∀ (b : κ) (e : Fin d), constantCoeff (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C) = 0 := by simp
  rw [subst_expPt G hs (fun e => by
    rw [Finset.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun b _ => cc_mv _ (cc_lgPt G (hX b)) e)]
  unfold expPt
  congr 1
  funext e
  rw [Finset.sum_apply, ← coe_substAlgHom hs, map_sum, coe_substAlgHom, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv hs]
  have h1 : (fun e' => subst (expAlong (fun _ : κ => G) u)
      (lgPt G (fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C)) e')) =
      fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C) := by
    funext e'
    rw [subst_lgPt G hs (hX b)]
    simp only [subst_X hs]
    rw [hE b, lgPt_expPt G (hu b)]
  rw [h1]
  simp only [mv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact congrFun (hA b a) e

theorem isotropic_blocks {O : Type} [CommRing O] [StarRing O] (I : Ideal O) {φ : Type} {r m : φ → ℕ} {n : ℕ}
    (blk : (Σ f : φ, Fin (m f)) ↪ Fin n) (ε : φ → O) (x : ∀ f, Fin (r f) → Fin n → O)
    (h0 : ∀ f b j, j ∉ Set.range (fun j => blk ⟨f, j⟩) → x f b j = 0)
    (hiso : ∀ f b b', ∑ j, x f b j * star (x f b' j) ∈ I) (b b' : Σ f, Fin (r f)) :
    ∑ j, star (ε b.1 * x b.1 b.2 j) * (ε b'.1 * x b'.1 b'.2 j) ∈ I := by
  obtain ⟨f, β⟩ := b
  obtain ⟨f', β'⟩ := b'
  by_cases hf : f = f'
  · subst hf
    have e : ∑ j, star (ε f * x f β j) * (ε f * x f β' j) =
        (star (ε f) * ε f) * ∑ j, x f β' j * star (x f β j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul]; ring
    rw [e]
    exact I.mul_mem_left _ (hiso f β' β)
  · refine Ideal.sum_mem _ fun j _ => ?_
    by_cases h1 : j ∈ Set.range (fun j => blk ⟨f, j⟩)
    · by_cases h2 : j ∈ Set.range (fun j => blk ⟨f', j⟩)
      · obtain ⟨j1, h1⟩ := h1
        obtain ⟨j2, h2⟩ := h2
        exact absurd (congrArg Sigma.fst (blk.injective (h1.trans h2.symm))) hf
      · simp [h0 f' β' j h2]
    · simp [h0 f β j h1]

theorem inclSt_of_lim (hAct : LimActSt) (hPt : LimPtSt) (hFr : LimFrameSt) : InclSt := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ Y cx n B hB
  obtain ⟨blk, hblk⟩ := hB
  choose x hx0 hxB hxiso using fun (f : {f : Lt1 Dw // cx f ≠ 0}) (N : ℕ) => (hblk f).2.2 N
  choose ε hε using fun τ : E →+* ℂ => hAct E H Dw l Xo c hstar T io y Ch p Y τ
  choose A hAapp hAlie using fun (b : Col cx) (j : Fin n) =>
    hε b.1.1.1 (B b.1.1 b.2 j) (fun N => x b.1 N b.2 j) (fun N => hxB b.1 N b.2 j)
  letI := io.toAlgebra
  letI : Algebra T.Fr Y.C := Y.ιF.toAlgebra
  have hw : ∀ b : Col cx, IntLog (fglOf (isIntFB_chart Ch Y)) (lgPt (fgl Ch Y)
      fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) Y.C)) :=
    fun b => intLog_lgPt_X (fgl Ch Y) (fun e => (⟨b, e⟩ : Σ _ : Col cx, Fin (chD Ch.ch)))
  have hint := fun j : Fin n => hPt Y.C (vX_vp Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (Col cx) _ hw
    (fun b => A b j) (fun N b => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b => hAapp b j N)
  refine ⟨fun q => expPt (fgl Ch Y) (∑ b, mv (A b q.1) (lgPt (fgl Ch Y) fun e => X ⟨b, e⟩)) q.2,
    fun q => cc_expPt _ (hint q.1).1 q.2, fun q => (hint q.1).2 q.2, fun q => ?_, ?_⟩
  · exact subst_expAlong (fgl Ch Y) (fun b : Col cx => frame Ch Y b.1.1) (fun b => A b q.1)
      (fun b => jX Y (B b.1.1 b.2 q.1)) (fun b a => hAlie b q.1 _) q.2
  · exact hFr Y.C (vX_vp Y) p (vX_vp_p Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (gauge_chart Ch Y) _ (Col cx) _
      hw H.w0 n A (fun N b j => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b j => hAapp b j N)
      (fun N => isotropic_blocks _ blk (fun f => ε f.1.1 N) (fun f => x f N) (fun f => hx0 f N)
        (fun f b b' => by simpa only [hstar] using hxiso f N b b'))

end GlobalTheory.IsoTriv.Incl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRetractionOfLimitSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem mv_sum_smul_X {C : Type} [Field C] {d : ℕ} {σ : Type} [Fintype σ] (A : Matrix (Fin d) (Fin d) C)
    (s : σ → C) (g : σ → Fin d → C) (e : Fin d) :
    mv A (fun e' => ∑ ℓ, (s ℓ * g ℓ e') • (MvPowerSeries.X ℓ : MvPowerSeries σ C)) e =
      ∑ ℓ, (s ℓ * A.mulVec (g ℓ) e) • (MvPowerSeries.X ℓ : MvPowerSeries σ C) := by
  simp only [mv, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun e' _ => ?_
  rw [mul_left_comm]

theorem subst_expPt_sum_mv {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : Fin n → Fin d → MvPowerSeries σ C) (hw : ∀ j e, constantCoeff (w j e) = 0)
    (r : κ → Fin n) (A : κ → Matrix (Fin d) (Fin d) C) (i : Fin d) :
    subst (fun q : Fin n × Fin d => expPt G (w q.1) q.2)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C))) i) =
      expPt G (fun e => ∑ b, mv (A b) (w (r b)) e) i := by
  have ht : HasSubst (fun q : Fin n × Fin d => expPt G (w q.1) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  have hl : ∀ b e, constantCoeff
      (lgPt G (fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C)) e) = 0 :=
    fun b => cc_lgPt G (by simp)
  rw [subst_expPt G ht (fun e => by
    rw [Finset.sum_apply, map_sum]; exact Finset.sum_eq_zero fun b _ => cc_mv _ (hl b) e)]
  congr 1
  funext e
  rw [Finset.sum_apply, ← coe_substAlgHom ht, map_sum, coe_substAlgHom]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv ht]
  congr 1
  funext e'
  rw [subst_lgPt G ht (by simp)]
  simp only [subst_X ht]
  exact congrFun (lgPt_expPt G (hw (r b))) e'

theorem retrSt_of : LimActSt → LimPtSt → InvSt → RetrSt := by
  intro hAct hPt hInv E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ X cx n B hB
  classical
  obtain ⟨blk, hblk⟩ := hB
  have key : ∀ f : {f : Lt1 Dw // cx f ≠ 0}, ∃ ρf : Fin (rk f.1) → Fin (chD Ch.ch) → PS X.C n (chD Ch.ch),
      (∀ β i, constantCoeff (ρf β i) = 0) ∧ (∀ β i, MvIsInt (vX_vp X) (ρf β i)) ∧
      ∀ β i, subst (colPt Ch X cx B) (ρf β i) = expH Ch X cx ⟨⟨f, β⟩, i⟩ := by
    intro f
    obtain ⟨hS, ⟨r, hr⟩, hx⟩ := hblk f
    obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c f.1.1))
    have inj := IsFractionRing.injective T.V T.Fr
    have hp0 : (p : T.V) ≠ 0 := fun h => by
      have h1 := congrArg (jX X) h
      rw [map_natCast, map_zero] at h1
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)
    have hM : ∀ b b' (N : ℕ), ∃ a z,
        φ a = (Matrix.of fun b b' => B f.1 b (r b')) b b' + φ (p : 𝓞 E) ^ N * z := fun b b' N => by
      obtain ⟨x, -, hx2, -⟩ := hx N
      obtain ⟨z, hz⟩ := hx2 b (r b')
      exact ⟨x b (r b'), z, inj (by rw [hφ, map_natCast φ]; exact hz)⟩
    obtain ⟨M', hMM', hM'⟩ := hInv (𝓞 E) T.V φ (p : 𝓞 E) (by rw [map_natCast]; exact hp0)
      (by rw [map_natCast]; exact not_isUnit_p X) (rk f.1) _ hr hM
    obtain ⟨ε, hε⟩ := hAct E H Dw l Xo c hstar T io y Ch p X f.1.1
    choose x z hxz using hM'
    choose A hA1 hA2 using fun β' β => hε (M' β' β) (x β' β) fun N =>
      ⟨z β' β N, by rw [← map_natCast φ p, ← hxz, hφ]; rfl⟩
    have hint : ∀ β, IntLog (fgl Ch X) (∑ β', mv (A β' β)
        (lgPt (fgl Ch X) fun e => (MvPowerSeries.X (r β', e) : PS X.C n (chD Ch.ch)))) := fun β => by
      letI := io.toAlgebra
      letI : Algebra T.Fr X.C := X.ιF.toAlgebra
      exact hPt X.C (vX_vp X) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (Fin (rk f.1)) _
        (fun β' => intLog_lgPt_X (fgl Ch X) fun e => (r β', e)) (fun β' => A β' β)
        (fun N β' => ε N * x β' β N) fun N β' => hA1 β' β N
    have hz : ∀ f' : {f : Lt1 Dw // cx f ≠ 0}, f' ≠ f → ∀ b β', B f'.1 b (r β') = 0 := fun f' hf b β' => by
      refine (hblk f').1 b _ fun ⟨j', hj'⟩ => ?_
      by_cases hm : r β' ∈ Set.range fun j => blk ⟨f, j⟩
      · obtain ⟨j, hj⟩ := hm
        exact hf (congrArg Sigma.fst (blk.injective (hj'.trans hj.symm)))
      · rw [Matrix.det_eq_zero_of_column_eq_zero β' fun b => hS b _ hm] at hr
        exact not_isUnit_zero hr
    refine ⟨fun β => expPt (fgl Ch X) _, fun β => cc_expPt _ (hint β).1, fun β => (hint β).2, fun β i => ?_⟩
    refine (subst_expPt_sum_mv (fgl Ch X) (fun j e => ∑ ℓ : Let cx,
      (jX X (B ℓ.1.1.1 ℓ.1.2 j) * frame Ch X ℓ.1.1.1 ℓ.2 e) • (MvPowerSeries.X ℓ : MvPowerSeries (Let cx) X.C))
      (fun j e => by simp) r (fun β' => A β' β) i).trans ?_
    show expPt _ _ i = expPt (fgl Ch X) (fun e => ∑ a, frame Ch X f.1 a e •
      (MvPowerSeries.X ⟨⟨f, β⟩, a⟩ : MvPowerSeries (Let cx) X.C)) i
    congr 1
    funext e
    simp only [mv_sum_smul_X]
    have hc : ∀ (b : Fin (rk f.1)) (a : Fin (rk f.1)),
        ∑ β', jX X (B f.1 b (r β')) * (A β' β).mulVec (frame Ch X f.1 a) e =
          if b = β then frame Ch X f.1 a e else 0 := fun b a => by
      have h1 := congrArg (jX X) (congrFun (congrFun hMM' b) β)
      rw [Matrix.mul_apply, map_sum, Matrix.one_apply] at h1
      simp only [frame, hA2, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Finset.sum_mul, ← map_mul]
      rw [show ∑ β', jX X (B f.1 b (r β') * M' β' β) = _ from h1]
      split_ifs <;> simp
    rw [Finset.sum_comm, Fintype.sum_sigma, Finset.sum_eq_single (⟨f, β⟩ : Col cx)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_smul, hc, if_pos rfl]
    · rintro ⟨f', b⟩ - hne
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.sum_smul]
      by_cases hf : f' = f
      · subst hf
        rw [hc, if_neg fun h => hne (by rw [show b = β from h]), zero_smul]
      · simp [hz f' hf]
    · exact fun h => absurd (Finset.mem_univ _) h
  choose ρf h1 h2 h3 using key
  exact ⟨fun q => ρf q.1.1 q.1.2 q.2, fun q => h1 _ _ _, fun q => h2 _ _ _, fun q => h3 _ _ _⟩

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteDvrPointLifting
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.FactorDepth

theorem trdegGe_map_of_ringHom {k k' : Type} [Field k] [Field k'] (φ : k →+* k') {n : ℕ} (h : TrdegGe k n) :
    TrdegGe k' n := by
  obtain ⟨t, ht⟩ := h
  have hm : (⊥ : Subfield k).map φ = ⊥ := Subfield.map_bot φ
  let f : (⊥ : Subfield k) →+* (⊥ : Subfield k') :=
    (φ.comp (⊥ : Subfield k).subtype).codRestrict _ fun x => hm ▸ ⟨x.1, x.2, rfl⟩
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx, e⟩ : y.1 ∈ (⊥ : Subfield k).map φ := hm.symm ▸ y.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  exact ⟨φ ∘ t, ht.ringHom_of_comp_eq f φ hf φ.injective (by ext; rfl)⟩

theorem exists_specializes_over_closedPoint (O : Type) [CommRing O] [IsLocalRing O] (X : Scheme.{0})
    (s : X ⟶ Sp O) [IsProper s] (x : X) : ∃ ξ : X, x ⤳ ξ ∧ s ξ = closedPoint O := by
  have h1 : s x ⤳ closedPoint O := IsLocalRing.specializes_closedPoint _
  obtain ⟨ξ, h2, h3⟩ := s.isClosedMap.specializingMap h1
  exact ⟨ξ, h2, h3⟩

theorem exists_cdvr_centred_trdegGe (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (X : Scheme.{0}) (s : X ⟶ Sp O) [IsProper s] (K : Type) [Field K] (g : Sp K ⟶ X) [IsPreimmersion g]
    (a : O →+* K) (ha : Function.Injective a) (hg : g ≫ s = spMap a) (d : ℕ)
    (hd : letI := a.toAlgebra; (d : Cardinal) ≤ Algebra.trdeg O K) :
    ∃ (T : CDVR) (yt : Sp T.V ⟶ X) (ψ : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b ∧ yt ≫ s = spMap b ∧
      spMap (algebraMap T.V T.Fr) ≫ yt = spMap ψ ≫ g ∧ TrdegGe (X.residueField (yt (closedPoint T.V))) d := by
  obtain ⟨ξ, hξ, hs⟩ := exists_specializes_over_closedPoint O X s (g (closedPoint K))
  obtain ⟨A, _, j, _, p, rfl⟩ : ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X) (_ : IsOpenImmersion j)
      (p : PrimeSpectrum A), j p = ξ := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ξ) isOpen_univ
    have hU : IsAffineOpen U := hU
    have : ξ ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    obtain ⟨p, hp⟩ := this
    exact ⟨Γ(X, U), inferInstance, hU.fromSpec, inferInstanceAs (IsOpenImmersion hU.fromSpec), p, hp⟩
  have hr : Set.range g ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (closedPoint K)]
    exact hξ.mem_open j.isOpenEmbedding.isOpen_range ⟨p, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : A →+* K, spMap φ ≫ j = g :=
    ⟨(Spec.preimage (IsOpenImmersion.lift j g hr)).hom, by
      rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨α, hα⟩ : ∃ α : O →+* A, spMap α = j ≫ s :=
    ⟨(Spec.preimage (j ≫ s)).hom, by rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have hcomp : φ.comp α = a := by
    have : spMap (φ.comp α) = spMap a := by
      rw [← hg, ← hφ, Category.assoc, ← hα, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  let _ := a.toAlgebra
  let _ := φ.toAlgebra
  let _ := α.toAlgebra
  have : IsScalarTower O A K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hft : Algebra.FiniteType O A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom α)).mp
      (show LocallyOfFiniteType (spMap α) from hα ▸ inferInstance)
  have hpre : IsPreimmersion (spMap φ) := by
    have : IsPreimmersion (spMap φ ≫ j) := hφ ▸ inferInstance
    exact IsPreimmersion.of_comp _ j
  have hst : φ.SurjectiveOnStalks := ((IsPreimmersion.SpecMap_iff (CommRingCat.ofHom φ)).1 hpre).2
  have hfr : ∀ x : K, ∃ u v : A, algebraMap A K v ≠ 0 ∧ x * algebraMap A K v = algebraMap A K u := fun x => by
    obtain ⟨u, v, c, hc, hv, e⟩ := RingHom.surjectiveOnStalks_iff_forall_ideal.1 hst ⊥ bot_ne_top x
    refine ⟨u, v, hv, mul_left_cancel₀ (show c ≠ 0 from hc) ?_⟩
    rw [mul_comm x, ← mul_assoc]
    exact e
  have hker : RingHom.ker (algebraMap A K) ≤ p.asIdeal := by
    have h1 : j (spMap φ (closedPoint K)) ⤳ j p := by
      rw [← hφ] at hξ
      exact hξ
    have h2 := (PrimeSpectrum.le_iff_specializes (PrimeSpectrum.comap φ (closedPoint K)) p).mpr
      (j.isOpenEmbedding.isInducing.specializes_iff.mp h1)
    exact fun x hx => h2 (show φ x ∈ (closedPoint K).asIdeal from (show φ x = 0 from hx) ▸ Ideal.zero_mem _)
  have hmax : (maximalIdeal O).map (algebraMap O A) ≤ p.asIdeal := by
    have h1 : (j ≫ s) p = closedPoint O := hs
    rw [← hα] at h1
    exact Ideal.map_le_iff_le_comap.2 (congrArg PrimeSpectrum.asIdeal h1).ge
  obtain ⟨T, f, ψ, e, hl, ht⟩ := GlobalTheory.T.valuation_ring_prime_dominance O A K ha hfr p.asIdeal p.isPrime hker hmax d hd
  refine ⟨T, spMap f ≫ j, ψ, f.comp α, hl, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hα, spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  · rw [← hφ, ← Category.assoc, ← Category.assoc, spMap, spMap, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  · let q : Sp A := PrimeSpectrum.comap f (closedPoint T.V)
    exact trdegGe_map_of_ringHom (k := q.asIdeal.ResidueField) (k' := X.residueField (j q))
      ((Scheme.Spec.residueFieldIso (.of A) q).inv ≫ inv (j.residueFieldMap q)).hom ht

end GlobalTheory.FactorDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedHomLattice_multiple_mem_open_level : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • u ∈ U) ∧ ∀ (g : GA D S) (h : GA D T), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.LatLevel.level_of_generators | exact GlobalTheory.LatLevel.level_of_generators | (intros; apply GlobalTheory.LatLevel.level_of_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeTsumPowNeZeroOfSingleUnitStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ge_tsum_pow_ne_zero_of_single_unit : ∀ {ι : Type} (a : ι → ℂ) (i0 : ι) (k0 : ℕ), a i0 = 1 → (∀ i, ‖a i‖ ≤ 1) → (∀ i, i ≠ i0 → ‖a i‖ < 1) → Summable (fun i => ‖a i‖ ^ k0) → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ ∑' i, a i ^ k ≠ 0 := by
  first | exact @GlobalTheory.tsum_pow_eventually_ne_zero | exact GlobalTheory.tsum_pow_eventually_ne_zero | (intros; apply GlobalTheory.tsum_pow_eventually_ne_zero <;> assumption)
end

