import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedModelSelfDualLatticeInvariantLinearFo
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem mem_mixLat_iff {x : Matrix (Fin n') (Fin n) L} : x ∈ mixLat L n' n ↔ ∀ r c,
    (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧ (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) :=
  Iff.rfl

theorem pairing_mixLat (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x) (hδ : Valued.v δ = 1)
    (hψ0 : ∀ a ∈ intL L, σ a = a → ψ a = 1) {a b : Matrix (Fin n') (Fin n) L} (ha : a ∈ mixLat L n' n)
    (hb : b ∈ mixLat L n' n) : pairing σ δ ψ a b = 1 := by
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => mem_intL.2 ((hv x).trans_le hx)
  rw [mem_mixLat_iff] at ha hb
  have hS : ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := by
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hai := ha i j
    have hbi := hb i.rev j.rev
    simp only [Fin.val_rev] at hbi
    have := i.isLt
    have := j.isLt
    by_cases h1 : n' - n' / 2 ≤ i.1 ∨ n' / 2 ≤ i.1 ∧ j.1 < n / 2
    · rw [hai.1 h1, zero_mul]; exact zero_mem _
    by_cases h2 : n' - n' / 2 ≤ n' - (i.1 + 1) ∨ n' / 2 ≤ n' - (i.1 + 1) ∧ n - (j.1 + 1) < n / 2
    · rw [hbi.1 h2, map_zero, mul_zero]; exact zero_mem _
    exact mul_mem (hai.2 (by omega) (by omega)) (hs _ (hbi.2 (by omega) (by omega)))
  have hi : δ * ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := mul_mem (mem_intL.2 hδ.le) hS
  exact hψ0 _ (add_mem hi (hs _ hi)) (by rw [map_add, hσ, add_comm])

theorem exists_bad_entry (x : Matrix (Fin n') (Fin n) L)
    (hx : ¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) :
    ∃ r c, x r c ∉ intL L ∧ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) := by
  by_contra hc
  refine hx ⟨fun r c => if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c, fun r c =>
    ⟨fun e => by dsimp only; rw [if_pos (by omega)], fun e e' => by dsimp only; rw [if_pos (by omega)]; exact zero_mem _⟩,
    fun r c => ?_⟩
  show x r c - (if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c) ∈ intL L
  split_ifs with hb
  · rw [sub_zero]
    by_contra hi
    exact hc ⟨r, c, hi, hb⟩
  · rw [sub_self]; exact zero_mem _

variable {M : Type} [AddCommGroup M] [Module ℂ M]
variable {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} {ω : GU σ n × GU σ n' →* Module.End ℂ M} {s : M}

theorem IsStd.form_eq_zero (h : IsStd ϖ σ q δ ψ ρ ω s) (ℓ' : M →ₗ[ℂ] ℂ)
    (hℓ' : ∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) (x : Matrix (Fin n') (Fin n) L) (r : Fin n') (c : Fin n)
    (hx : x r c ∉ intL L) (hrc : n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) : ℓ' (ρ x s) = 0 := by
  obtain ⟨u, hu, hne⟩ := exists_pairing_single_ne h.1.unr h.v_two h.1.delta.1 h.1.psi_ne x hx
  have := r.isLt
  have := c.isLt
  have hyA : Matrix.single r.rev c.rev u ∈ mixLat L n' n := by
    intro r' c'
    rw [Matrix.single_apply]
    split_ifs with he
    · obtain ⟨rfl, rfl⟩ := he
      simp only [Fin.val_rev]
      exact ⟨fun e => by omega, fun _ _ => hu⟩
    · exact ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  have hyL : Matrix.single r.rev c.rev u ∈ intMat L (Fin n') (Fin n) := by
    intro i j
    rw [Matrix.single_apply]
    split_ifs
    exacts [hu, zero_mem _]
  have e1 := h.isHeis.comm x (Matrix.single r.rev c.rev u) s
  rw [h.fixes _ hyL] at e1
  have e2 := congrArg ℓ' e1
  rw [map_smul, hℓ' _ hyA, smul_eq_mul] at e2
  have e3 : (pairing σ δ ψ x (Matrix.single r.rev c.rev u) - 1) * ℓ' (ρ x s) = 0 := by linear_combination -e2
  rcases mul_eq_zero.1 e3 with h' | h'
  · exact absurd (sub_eq_zero.1 h') hne
  · exact h'

end

theorem exists_mixLat_form : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) ∧ (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) ∧ (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ℓ (ρ (embLow n' n z) s) = if z ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) then 1 else 0 := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s h
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum h.isHeis (intMat L (Fin n') (Fin n)) h.selfDual s h.2.1 h.fixes h.2.2.2
    (mixLat L n' n) fun a ha b hb => pairing_mixLat h.1.unr.1 h.1.unr.2.1 h.1.delta.1 h.1.psi_int ha hb
  have hz : ∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ x,
      (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ' (ρ x s) = 0 := fun ℓ' hℓ' x hx => by
    obtain ⟨r, c, hr, hrc⟩ := exists_bad_entry x hx
    exact h.form_eq_zero ℓ' hℓ' x r c hr hrc
  refine ⟨ℓ, h1, h2, hz ℓ h2, fun ℓ' hℓ' => ?_, fun z => ?_⟩
  · have key : ℓ' = ℓ' s • ℓ := LinearMap.ext_on_range h.2.2.2 fun x => ?_
    · exact fun v => LinearMap.congr_fun key v
    show ℓ' (ρ x s) = (ℓ' s • ℓ) (ρ x s)
    by_cases hx : ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)
    · obtain ⟨a, ha, hxa⟩ := hx
      have e := h.isHeis.comp a (x - a) s
      rw [h.fixes _ hxa, show a + (x - a) = x by abel] at e
      have hg := h.isHeis.ne_zero (half h.v_two • a) (x - a)
      have hx' : ρ x s = (pairing σ δ ψ (half h.v_two • a) (x - a))⁻¹ • ρ a s := by
        rw [e, smul_smul, inv_mul_cancel₀ hg, one_smul]
      rw [LinearMap.smul_apply, hx', map_smul, map_smul, hℓ' a ha, h2 a ha, h1, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        mul_one, mul_comm]
    · rw [LinearMap.smul_apply, hz ℓ' hℓ' x hx, hz ℓ h2 x hx, smul_zero]
  · have := (n' / 2).le_refl
    split_ifs with hzi
    · have hm : embLow n' n z ∈ intMat L (Fin n') (Fin n) := fun r c => by
        unfold embLow
        split_ifs
        exacts [hzi _ _, zero_mem _]
      rw [h.fixes _ hm, h1]
    · obtain ⟨i, j, hij⟩ : ∃ i j, z i j ∉ intL L := by
        by_contra hc
        push_neg at hc
        exact hzi hc
      have he : embLow n' n z (hi n' i) (hi n j) = z i j := by
        simp [embLow, hi]
      refine h.form_eq_zero ℓ h2 _ (hi n' i) (hi n j) (by rwa [he]) (Or.inl ?_)
      simp only [hi]
      omega

end GlobalTheory.SphTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicityMapPrescribedValueDefinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefFree

theorem exists_adForms_value {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (hχ : ∀ k, χ k = 1) (x₀ : G)
    (hfree : ∀ γ : Γ, ∀ k ∈ J, ι γ * x₀ = x₀ * k → γ = 1) (w : W) :
    ∃ f ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ, f x₀ = w ∧
      ∀ y, (¬ ∃ γ : Γ, ∃ k ∈ J, y = ι γ * x₀ * k) → f y = 0 := by
  classical

  have huniq : ∀ (γ γ' : Γ) (k k' : G), k ∈ J → k' ∈ J → ι γ * x₀ * k = ι γ' * x₀ * k' → γ = γ' := by
    intro γ γ' k k' hk hk' e
    have e' : ι (γ'⁻¹ * γ) * x₀ = x₀ * (k' * k⁻¹) := by
      calc ι (γ'⁻¹ * γ) * x₀ = (ι γ')⁻¹ * (ι γ * x₀ * k) * k⁻¹ := by rw [map_mul, map_inv]; group
        _ = (ι γ')⁻¹ * (ι γ' * x₀ * k') * k⁻¹ := by rw [e]
        _ = x₀ * (k' * k⁻¹) := by group
    exact (inv_mul_eq_one.mp (hfree _ _ (J.mul_mem hk' (J.inv_mem hk)) e')).symm
  have hval : ∀ (y : G) (hy : ∃ γ : Γ, ∃ k ∈ J, y = ι γ * x₀ * k) (γ : Γ) (k : G), k ∈ J → y = ι γ * x₀ * k →
      hy.choose = γ := by
    intro y hy γ k hk e
    obtain ⟨k₀, hk₀, e₀⟩ := hy.choose_spec
    exact huniq _ _ _ _ hk₀ hk (e₀.symm.trans e)
  refine ⟨fun y => if hy : ∃ γ : Γ, ∃ k ∈ J, y = ι γ * x₀ * k then ρ hy.choose w else 0, ?_, ?_, ?_⟩
  · show ∀ (γ : Γ) (h : G) (k : J), _ = _
    intro γ h k
    simp only [hχ, Units.val_one, one_smul]
    by_cases hh : ∃ γ₁ : Γ, ∃ k₁ ∈ J, h = ι γ₁ * x₀ * k₁
    · obtain ⟨γ₁, k₁, hk₁, rfl⟩ := hh
      have e2 : ι γ * (ι γ₁ * x₀ * k₁) * (k : G) = ι (γ * γ₁) * x₀ * (k₁ * k) := by
        rw [map_mul]; group
      have h2 : ∃ γ' : Γ, ∃ k' ∈ J, ι γ * (ι γ₁ * x₀ * k₁) * (k : G) = ι γ' * x₀ * k' :=
        ⟨γ * γ₁, k₁ * k, J.mul_mem hk₁ k.2, e2⟩
      have h1 : ∃ γ' : Γ, ∃ k' ∈ J, ι γ₁ * x₀ * k₁ = ι γ' * x₀ * k' := ⟨γ₁, k₁, hk₁, rfl⟩
      rw [dif_pos h2, dif_pos h1, hval _ h2 (γ * γ₁) (k₁ * k) (J.mul_mem hk₁ k.2) e2,
        hval _ h1 γ₁ k₁ hk₁ rfl, map_mul, Module.End.mul_apply]
    · have h2 : ¬ ∃ γ' : Γ, ∃ k' ∈ J, ι γ * h * (k : G) = ι γ' * x₀ * k' := by
        rintro ⟨γ', k', hk', e⟩
        refine hh ⟨γ⁻¹ * γ', k' * (k : G)⁻¹, J.mul_mem hk' (J.inv_mem k.2), ?_⟩
        calc h = (ι γ)⁻¹ * (ι γ * h * (k : G)) * (k : G)⁻¹ := by group
          _ = ι (γ⁻¹ * γ') * x₀ * (k' * (k : G)⁻¹) := by rw [e, map_mul, map_inv]; group
      rw [dif_neg h2, dif_neg hh, map_zero]
  · have h0 : ∃ γ : Γ, ∃ k ∈ J, x₀ = ι γ * x₀ * k := ⟨1, 1, J.one_mem, by simp⟩
    dsimp only
    rw [dif_pos h0, hval _ h0 1 1 J.one_mem (by simp), map_one, Module.End.one_apply]
  · intro y hy
    dsimp only
    rw [dif_neg hy]

theorem eq_one_of_gam_bot {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {n : ℕ} {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {K : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))}
    (hG : ∀ c₀ : Cl hc J K, Gam c₀ = ⊥) (x u : UA hc J) (hu : u ∈ UQ hc J)
    (hk : ((x⁻¹ * u * x : UA hc J) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K) : u = 1 := by
  rw [Subgroup.mem_subgroupOf] at hu
  simp only [Formalism.UG.ratPts, Subgroup.mem_map] at hu
  obtain ⟨g, hg, hgu⟩ := hu
  obtain ⟨q, hq, k₁, hk₁, e3⟩ := (DoubleCoset.eq (UQ hc J) (K.subgroupOf (UA hc J))
    (Formalism.L2.DIV.rep (Quotient.mk'' x : Cl hc J K)) x).1 (Formalism.L2.DIV.mk_rep _)
  rw [Subgroup.mem_subgroupOf] at hq hk₁
  simp only [Formalism.UG.ratPts, Subgroup.mem_map] at hq
  obtain ⟨gq, hgq, hgqe⟩ := hq
  have hmem : gq⁻¹ * g * gq ∈ Formalism.L2.DIV.UR hc J :=
    (Formalism.L2.DIV.UR hc J).mul_mem ((Formalism.L2.DIV.UR hc J).mul_mem ((Formalism.L2.DIV.UR hc J).inv_mem hgq) hg) hgq
  have hx : ((x : UA hc J) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      (q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (Formalism.L2.DIV.rep (Quotient.mk'' x : Cl hc J K) : UA hc J) * k₁ := by
    have h3 := congrArg Subtype.val e3
    simpa only [Subgroup.coe_mul] using h3
  have hk0 : (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * u * x ∈ K := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hk
  have hin : (⟨gq⁻¹ * g * gq, hmem⟩ : Formalism.L2.DIV.UR hc J) ∈ Formalism.L2.DIV.Gam (Quotient.mk'' x : Cl hc J K) := by
    show Formalism.L2.DIV.conjIn hc J _ _ ∈ K
    rw [Formalism.L2.DIV.conjIn_apply]
    have hr : ((Formalism.L2.DIV.rep (Quotient.mk'' x : Cl hc J K) : UA hc J) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * x * (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
      rw [hx]; group
    simp only [map_mul, map_inv, hgu, hgqe]
    rw [hr]
    have e4 : ((q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * x * (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹)⁻¹ *
        ((q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * u * q) *
        ((q : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * x * (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) =
        (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * u * x) *
          (k₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by group
    rw [e4]
    exact K.mul_mem (K.mul_mem hk₁ hk0) (K.inv_mem hk₁)
  have hb : (⟨gq⁻¹ * g * gq, hmem⟩ : Formalism.L2.DIV.UR hc J) ∈ (⊥ : Subgroup (Formalism.L2.DIV.UR hc J)) := by
    rw [← hG (Quotient.mk'' x)]
    exact hin
  have h1 : gq⁻¹ * g * gq = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hb)
  have hg1 : g = 1 := by
    calc g = gq * (gq⁻¹ * g * gq) * gq⁻¹ := by group
      _ = 1 := by rw [h1]; group
  apply Subtype.ext
  rw [← hgu, hg1, map_one]
  rfl

section

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem finE_of_eq {γ : GQ V} {h h' κ : GA D V} {k : Formalism.IndefR.Bridge.Gf V} (hk : finHom V κ = k.1)
    (e : (finHom V).rangeRestrict h' = Formalism.IndefR.Bridge.ratF V γ * (finHom V).rangeRestrict h * k) :
    finU V h' = finU V γ * finU V h * finU V κ := by
  apply Subtype.ext
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict, Formalism.IndefR.Bridge.ratF, MonoidHom.comp_apply,
    Subgroup.coe_subtype] at e'
  simp only [Subgroup.coe_mul, coe_finU, finE_eq, e', hk, map_mul]

theorem finE_mem_lev {κ : GA D V} {k : Formalism.IndefR.Bridge.Gf V} (hk : finHom V κ = k.1) (h : k ∈ (levEnv V β L).J) :
    finE V κ ∈ lev D.sp.cm V.gram β (flag1L L) := by
  rw [finE_eq, hk]
  exact h

theorem stab_trivial (hG : ∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) (h : GA D V)
    (γ : GQ V) (k : Formalism.IndefR.Bridge.Gf V) (hk : k ∈ (levEnv V β L).J)
    (e : Formalism.IndefR.Bridge.ratF V γ * (finHom V).rangeRestrict h = (finHom V).rangeRestrict h * k) : γ = 1 := by
  obtain ⟨κ, hκ⟩ := MonoidHom.mem_range.1 k.2
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict, Formalism.IndefR.Bridge.ratF, MonoidHom.comp_apply,
    Subgroup.coe_subtype] at e'
  have hk' : (k : GL (Fin V.rank) _) = (finHom V h)⁻¹ * finHom V γ * finHom V h := by
    rw [mul_assoc, e']; group
  have key : (((finU V h)⁻¹ * finU V γ * finU V h : UA D.sp.cm V.gram) : GL (Fin V.rank) (EAf D)) = finE V κ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_finU, finE_eq, hκ, hk', map_mul, map_inv]
  have hu := eq_one_of_gam_bot hG (finU V h) (finU V γ) (AdelCls.rat_mem V γ γ.2)
    (by rw [key]; exact finE_mem_lev hκ hk)
  exact Subtype.ext (AdelCls.rat_inj V γ γ.2 hu)

set_option maxHeartbeats 1000000 in
private theorem clsA_eq_of_ratF_mul {h h' : GA D V} {γ : GQ V} {k : Formalism.IndefR.Bridge.Gf V} (hk : k ∈ (levEnv V β L).J)
    (e : (finHom V).rangeRestrict h' = Formalism.IndefR.Bridge.ratF V γ * (finHom V).rangeRestrict h * k) :
    clsA V (lev D.sp.cm V.gram β (flag1L L)) h' = clsA V (lev D.sp.cm V.gram β (flag1L L)) h := by
  obtain ⟨κ, hκ⟩ := MonoidHom.mem_range.1 k.2
  have h1 := finE_of_eq hκ e
  have h2 := finE_mem_lev hκ hk
  obtain ⟨κ', hκ'G, hκ'⟩ := AdelCls.exists_fin V (finU V κ)
  refine (((AdelCls.adelic_classes D V).2.2.2.2 _ h h').2 ⟨γ, γ.2, κ', ?_, (↑γ * h * κ')⁻¹ * h', ?_, by group⟩).symm
  · refine Formalism.IndefR.Lev.mem_levA.2 ⟨hκ'G, ?_⟩
    rw [← coe_finU, hκ', coe_finU]
    exact h2
  · refine (AdelCls.finU_eq_one_iff V _).1 ?_
    apply Subtype.ext
    have h1' : finE V h' = finE V ↑γ * finE V h * finE V κ := by
      simpa only [Subgroup.coe_mul, coe_finU] using congrArg Subtype.val h1
    have hκ'' : finE V κ' = finE V κ := by
      simpa only [coe_finU] using congrArg Subtype.val hκ'
    rw [coe_finU, OneMemClass.coe_one]
    simp only [map_mul, map_inv, h1', hκ'']
    group

theorem clsA_eq_of_eq {h h' : GA D V} {γ : GQ V} {k : Formalism.IndefR.Bridge.Gf V} (hk : k ∈ (levEnv V β L).J)
    (e : (finHom V).rangeRestrict h' = Formalism.IndefR.Bridge.ratF V γ * (finHom V).rangeRestrict h * k) :
    clsA V (lev D.sp.cm V.gram β (flag1L L)) h' = clsA V (lev D.sp.cm V.gram β (flag1L L)) h := by
  exact clsA_eq_of_ratF_mul hk e

theorem exists_form_value (c : CoefA V) (hχ : ∀ x, levFn β (flag1L L) x = 1)
    (hG : ∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) (h : GA D V) (w : c.W) :
    ∃ f : Formalism.IndefR.Bridge.Gf V → c.W,
      f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ ∧
      f ((finHom V).rangeRestrict h) = w ∧
      ∀ h' : GA D V, clsA V (lev D.sp.cm V.gram β (flag1L L)) h' ≠ clsA V (lev D.sp.cm V.gram β (flag1L L)) h →
        f ((finHom V).rangeRestrict h') = 0 := by
  have hχ' : ∀ q, (levEnv V β L).χ q = 1 := fun q => hχ _
  obtain ⟨f, hf, hfx, hf0⟩ := exists_adForms_value (W := c.W) (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J
    (levEnv V β L).χ hχ' ((finHom V).rangeRestrict h) (fun γ q hq e => stab_trivial hG h γ q hq e) w
  refine ⟨f, hf, hfx, fun h' hne => hf0 _ ?_⟩
  rintro ⟨γ, q, hq, e⟩
  exact hne (clsA_eq_of_eq hq e)

set_option maxHeartbeats 1000000 in
private theorem apply_rangeRestrict_mul_eq_of_mem_adForms_of_mem_levS {c : CoefA V} (hχ : ∀ x, levFn β (flag1L L) x = 1) {f : Formalism.IndefR.Bridge.Gf V → c.W}
    (hf : f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (g : GA D V) {k : GA D V} (hk : k ∈ levS V β (flag1L L)) :
    f ((finHom V).rangeRestrict (g * k)) = f ((finHom V).rangeRestrict g) := by
  have hf' : ∀ (γ : GQ V) (x : Formalism.IndefR.Bridge.Gf V) (q : (levEnv V β L).J),
      f (Formalism.IndefR.Bridge.ratF V γ * x * q) = ((levEnv V β L).χ q : ℂ) • c.coef.ρ γ (f x) := hf
  have hk0 : k ∈ levA V (lev D.sp.cm V.gram β (flag1L L)) := hk
  have hk' : finE V k ∈ lev D.sp.cm V.gram β (flag1L L) := (Formalism.IndefR.Lev.mem_levA.1 hk0).2
  have hJ : (finHom V).rangeRestrict k ∈ (levEnv V β L).J := by
    show Formalism.UG.bc (swapAE D) (finHom V k) ∈ lev D.sp.cm V.gram β (flag1L L)
    rw [← finE_eq]
    exact hk'
  have e1 := hf' 1 ((finHom V).rangeRestrict g) ⟨_, hJ⟩
  have hc1 : (levEnv V β L).χ ⟨_, hJ⟩ = 1 := hχ (Formalism.UG.bc (swapAE D) (finHom V k))
  rw [map_one, one_mul, map_one, hc1, Units.val_one, one_smul] at e1
  rw [map_mul]
  exact e1

theorem form_mul_level {c : CoefA V} (hχ : ∀ x, levFn β (flag1L L) x = 1) {f : Formalism.IndefR.Bridge.Gf V → c.W}
    (hf : f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (g : GA D V) {k : GA D V} (hk : k ∈ levS V β (flag1L L)) :
    f ((finHom V).rangeRestrict (g * k)) = f ((finHom V).rangeRestrict g) := by
  exact apply_rangeRestrict_mul_eq_of_mem_adForms_of_mem_levS hχ hf g hk

theorem toMap_apply {S : D.what₂.Tau → SPar} {M : DSModel V S} (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)
    (f : Formalism.IndefR.Bridge.Gf V → c.W) (v : M.Vec) (g : GA D V) : PiTensorProduct.lift.symm (c.toMap pr f) v g =
      pr (c.ρ g⁻¹ (f ((finHom V).rangeRestrict g))) (PiTensorProduct.tprod ℂ v) := rfl

set_option maxHeartbeats 1000000 in
private theorem exists_mult_evAt_eq_and_vanish_off_class : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsInfFam θ → V.SigOK → V.IsDefinite → c.Is → IsDualPair θ M c pr → Function.Surjective pr → (∀ x, levFn β (flag1L L) x = 1) → (∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) → ∀ (h : GA D V) (ℓ : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∃ T ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)), evAt M h T = ℓ ∧ ∀ h' : GA D V, clsA V (lev D.sp.cm V.gram β (flag1L L)) h' ≠ clsA V (lev D.sp.cm V.gram β (flag1L L)) h → evAt M h' T = 0 := by
  intro D θ V S M c pr β L hθ hs hd hc hpr hsurj hχ hG h ℓ
  obtain ⟨w, hw⟩ := hsurj (PiTensorProduct.lift ℓ)
  obtain ⟨f, hf, hfx, hf0⟩ := exists_form_value c hχ hG h (c.ρ h w)
  have hM := GlobalTheory.DefiniteEnd.isMultMap_toMap hθ hs hd M hc hpr hf
  have hval : ∀ (v : M.Vec) (g : GA D V), PiTensorProduct.lift.symm (c.toMap pr f) v g =
      pr (c.ρ g⁻¹ (f ((finHom V).rangeRestrict g))) (PiTensorProduct.tprod ℂ v) :=
    fun v g => toMap_apply c pr f v g
  have hinv : c.ρ h⁻¹ (c.ρ h w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine ⟨PiTensorProduct.lift.symm (c.toMap pr f), Submodule.subset_span ?_, ?_, ?_⟩
  · show IsMultMap θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) _
    refine { hM with lev := ?_ }
    intro v k hk g
    have hk0 : k ∈ levA V (lev D.sp.cm V.gram β (flag1L L)) := hk
    have hk' : k ∈ GfC V ∧ finE V k ∈ lev D.sp.cm V.gram β (flag1L L) := Formalism.IndefR.Lev.mem_levA.1 hk0
    have hchi : levChi V β (flag1L L) k = 1 := by
      show ((Formalism.L2.DIV.levFn β (flag1L L) (finE V k) : ℂˣ) : ℂ) = 1
      rw [hχ, Units.val_one]
    have hρ : c.ρ k⁻¹ = 1 := hc.1 _ ((GfC V).inv_mem hk'.1)
    rw [hval, hval, hchi, one_mul, form_mul_level hχ hf g hk, mul_inv_rev, map_mul, Module.End.mul_apply, hρ,
      Module.End.one_apply]
  · ext v
    rw [evAt_apply, hval, hfx, hinv, hw, PiTensorProduct.lift.tprod]
  · intro h' hne
    ext v
    rw [evAt_apply, hval, hf0 h' hne, map_zero, map_zero, LinearMap.zero_apply, MultilinearMap.zero_apply]

end

theorem exists_mult_value : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsInfFam θ → V.SigOK → V.IsDefinite → c.Is → IsDualPair θ M c pr → Function.Surjective pr → (∀ x, levFn β (flag1L L) x = 1) → (∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) → ∀ (h : GA D V) (ℓ : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∃ T ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)), evAt M h T = ℓ ∧ ∀ h' : GA D V, clsA V (lev D.sp.cm V.gram β (flag1L L)) h' ≠ clsA V (lev D.sp.cm V.gram β (flag1L L)) h → evAt M h' T = 0 := by
  exact exists_mult_evAt_eq_and_vanish_off_class

end GlobalTheory.DefFree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_standard_pair_member_has_theta_function : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A WW : HSp D) (rA : Rig A) (rW : Rig WW) (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Pl D.host.E)) (I : Ideal (𝓞 D.host.E)) (vac : WO A WW → ℂ), rA.Is → rW.Is → IsHeckeChar D ν → IsIdemSum e S → I ≠ ⊥ → IsVacO ψ θ (neg A) WW (fun τ => -rA.s τ) rW.s rA.Λ rW.Λ vac → ∃ f, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) e (latO (neg A) WW rA.Λ rW.Λ fun _ => True) 1 vac (stdFst ν e I A WW rA.β rW.β) f ∧ IsThetaFunO ψ (neg A) WW f := by
  first | exact @GlobalTheory.Adopt.first_standard_pair_member_has_theta_function | exact GlobalTheory.Adopt.first_standard_pair_member_has_theta_function | (intros; apply GlobalTheory.Adopt.first_standard_pair_member_has_theta_function <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
section
noncomputable section

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def blockB (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.fst ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

def blockD (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.snd ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

theorem blockB_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockB J q = (J (0, q)).1 := rfl

theorem blockD_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockD J q = (J (0, q)).2 := rfl

def fockForm (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply]; push_cast; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.real_smul]; push_cast; ring)
    (fun x y y' => by simp only [map_add]; push_cast; ring)
    (fun c x y => by simp only [map_smul, smul_eq_mul, Complex.real_smul]; push_cast; ring)

theorem fockForm_apply (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (x y : V) :
    fockForm β J x y = ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ) := rfl

end GlobalTheory.FockFamily

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorsReframeSourceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVectors_reframeSource : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, ∃ BS' : D.what₂.Tau → Matrix (Fin (reS S b).rank) (Fin (reS S b).rank) ℂ, (∀ τ, (BS' τ)ᴴ * gramAt D (reS S b) τ * BS' τ = (BS τ)ᴴ * gramAt D S τ * BS τ) ∧ ∀ (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ (reS S b) T (fun _ => 1) sT BS' BT (reF S T b f) P = reF S T b (pureTensorO ψ θ S T (fun _ => 1) sT BS BT f P) := by
  first | exact @GlobalTheory.AdSpan.pureTensorO_reF | exact GlobalTheory.AdSpan.pureTensorO_reF | (intros; apply GlobalTheory.AdSpan.pureTensorO_reF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FreeMonoidAlgebraOfCharacterVanishesOffOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_monoidAlgebra_of_character_vanishes_off_one : ∀ (P M : Type) [Group P] [Finite P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ P M), (∀ g : P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) → ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M ∧ Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra ℂ P] (Fin N → MonoidAlgebra ℂ P)) := by
  first | exact @GlobalTheory.FreeOfCharacter.free_of_trace_eq_zero | exact GlobalTheory.FreeOfCharacter.free_of_trace_eq_zero | (intros; apply GlobalTheory.FreeOfCharacter.free_of_trace_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorCoeffEqProdAtTwoTypePrimesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_e0_eq_eGood_mul_eGood : ∀ (D : D7) (τ : ∀ k : Fin 2, (ZMod (D.host.g k))[X] → GlobalTheory.BadShare.GG (D.host.g k) D.R.r → ℂ), (∀ k, ∀ f ∈ GlobalTheory.BadShare.sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = GlobalTheory.BadShare.zc (τ k f) x) → ∀ γ : G0g D.nd, D.ntypes.e0.coeff γ = GlobalTheory.BadShare.eGood (fun _ => τ 0) (D.nd.chiT 0) (fun v => γ ⟨0, v⟩) * GlobalTheory.BadShare.eGood (fun _ => τ 1) (D.nd.chiT 1) (fun v => γ ⟨1, v⟩) := by
  first | exact @GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes | exact GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes | (intros; apply GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompactOpenTypeIdempotentUnipotentEqZeroStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_compactOpenTypeIdempotent_unipotent_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W)
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k))
    (N : Subgroup (GL (Fin r) k)) (ν : Measure N) [ν.IsMulLeftInvariant] (H : Subgroup (GL (Fin r) 𝓀[k])),
    NoFixed τ H → ∀ x : GL (Fin r) k,
    (∀ v ∈ H, ∃ n ∈ N, ∃ hn : x * n * x⁻¹ ∈ KO k (Fin r), GlobalTheory.LocGL.redK k (Fin r) ⟨x * n * x⁻¹, hn⟩ = v) →
    ∀ w : GL (Fin r) k, ∫ u : N, idemGL k μ τ (x * u * w) ∂ν = 0 := by
  first | exact @GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero | exact GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero | (intros; apply GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjectiveStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModule_map_injective_of_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W) (f : π₁.IntertwiningMap π), IsSmooth π → Function.Injective f → Function.Injective (jacMap e f) := by
  first | exact @GlobalTheory.JacInj.jacMap_injective | exact GlobalTheory.JacInj.jacMap_injective | (intros; apply GlobalTheory.JacInj.jacMap_injective <;> assumption)
end

