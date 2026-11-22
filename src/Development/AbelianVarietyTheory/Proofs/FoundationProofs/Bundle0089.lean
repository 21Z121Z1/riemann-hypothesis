import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerPadicCompletionMapEvalDependsOnLevel
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.LevelRed

open scoped MatrixGroups TensorProduct in
open Matrix in

theorem _root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd {M M0 : ℕ} (h : M ∣ M0) :
    CongruenceSubgroup.Gamma M0 ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ z : ℤ, ((z : ZMod M0).cast : ZMod M) = z := ZMod.cast_intCast h
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key, h1, ZMod.cast_one h]
  · rw [← key, h2, ZMod.cast_zero]
  · rw [← key, h3, ZMod.cast_zero]
  · rw [← key, h4, ZMod.cast_one h]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

noncomputable abbrev bc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Kl l →ₗ[ℤ_[l]] X.Kl l :=
  LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))

end GlobalTheory.KZ.LevelRed

namespace GlobalTheory.KZ

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma exists_level_bc_eq_of_agree_on_level {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ) [Fact l.Prime] (m : X.Kl l) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K,
      (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0,
        X.sl (_root_.GlobalTheory.KZ.ofSL γ) f = f) → φ f = ψ f) →
      _root_.GlobalTheory.KZ.LevelRed.bc X l φ m = _root_.GlobalTheory.KZ.LevelRed.bc X l ψ m := by
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, fun φ ψ _ => by simp⟩
  | tmul c u =>
    obtain ⟨M, hM, hfix⟩ := X.level ((Additive.toMul u : X.Kˣ) : X.K)
    refine ⟨M, hM, fun φ ψ h => ?_⟩
    have hu : Units.map φ.toMonoidHom (Additive.toMul u) =
        Units.map ψ.toMonoidHom (Additive.toMul u) :=
      Units.ext (by simpa using h _ hfix)
    simp only [LinearMap.baseChange_tmul]
    congr 1
  | add x y hx hy =>
    obtain ⟨M1, hM1, h1⟩ := hx
    obtain ⟨M2, hM2, h2⟩ := hy
    refine ⟨M1 * M2, Nat.mul_pos hM1 hM2, fun φ ψ h => ?_⟩
    rw [map_add, map_add,
      h1 φ ψ fun f hf => h f fun γ hγ => hf γ (_root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd (dvd_mul_right M1 M2) hγ),
      h2 φ ψ fun f hf => h f fun γ hγ => hf γ (_root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd (dvd_mul_left M2 M1) hγ)]

open scoped MatrixGroups TensorProduct in
open Matrix in

theorem _root_.GlobalTheory.KZ.Tower.eval_kmap_levelRed : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (n : ℕ), ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K, (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0, X.sl (_root_.GlobalTheory.KZ.ofSL γ) f = f) → φ f = ψ f) → AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n (X.kmap l φ a) = AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n (X.kmap l ψ a) := by
  intro Ω _ _ ε X l _ a n
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (a.1 n)
  obtain ⟨M0, hM0, hlev⟩ := exists_level_bc_eq_of_agree_on_level X l m
  refine ⟨M0, hM0, fun φ ψ h => ?_⟩
  unfold _root_.GlobalTheory.KZ.Tower.kmap
  simp only [LinearMap.coe_restrictScalars, AdicCompletion.map_val_apply,
    AdicCompletion.eval_apply]
  rw [← hm]
  simp only [LinearMap.reduceModIdeal_apply]
  exact congrArg _ (hlev φ ψ h)

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceCompLeftFunLeft
section
open Polynomial Classical GlobalTheory.BadShare

noncomputable section
namespace GlobalTheory.BadShare

theorem trace_compLeft_funLeft {G W : Type} [Fintype G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : W →ₗ[ℂ] W) (f : G → G) :
    LinearMap.trace ℂ (G → W) (A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f) =
      ∑ x, if f x = x then LinearMap.trace ℂ W A else 0 := by
  have h : A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f =
      ∑ x, LinearMap.single ℂ (fun _ : G => W) x ∘ₗ (A ∘ₗ LinearMap.proj (f x)) := by
    refine LinearMap.ext fun φ => funext fun y => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, LinearMap.funLeft_apply]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.trace_comp_comm']
  split_ifs with hx
  · congr 1
    ext w
    simp [hx]
  · have : (A ∘ₗ LinearMap.proj (f x)) ∘ₗ LinearMap.single ℂ (fun _ : G => W) x = 0 := by
      ext w
      simp [hx]
    rw [this, map_zero]

section
variable {G : Type} [Group G] [Fintype G] {Γ : Type} [Group Γ] [Fintype Γ] (r : Γ →* G)
  {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ Γ W)

def coindSum : (G → W) →ₗ[ℂ] Representation.coindV r σ :=
  LinearMap.codRestrict _
    (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) (by
      intro φ δ x
      simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.compLeft_apply,
        Function.comp_apply, LinearMap.funLeft_apply, map_sum]
      refine Fintype.sum_equiv (Equiv.mulRight δ) _ _ fun γ => ?_
      simp only [Equiv.coe_mulRight, map_mul r, mul_assoc, mul_inv_rev]
      rw [← Module.End.mul_apply, ← map_mul σ, mul_inv_cancel_left])

omit [Fintype G] [FiniteDimensional ℂ W] in
theorem coindSum_apply (φ : G → W) (x : G) :
    (coindSum r σ φ).1 x = ∑ γ : Γ, σ γ⁻¹ (φ (r γ * x)) := by
  change (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) φ x = _
  simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]

theorem trace_coind_mul_card (g : G) :
    LinearMap.trace ℂ _ (Representation.coind r σ g) * (Fintype.card Γ : ℂ) =
      ∑ γ : Γ, ∑ x : G, if r γ * (x * g) = x then LinearMap.trace ℂ W (σ γ⁻¹) else 0 := by
  have h1 : (Fintype.card Γ : ℂ) • (Representation.coind r σ g : _ →ₗ[ℂ] _) =
      coindSum r σ ∘ₗ (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    rw [LinearMap.comp_apply, coindSum_apply]
    have : ∀ γ : Γ, σ γ⁻¹ ((LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) φ (r γ * x))
        = φ.1 (x * g) := by
      intro γ
      change σ γ⁻¹ (φ.1 (r γ * x * g)) = _
      rw [mul_assoc, φ.2 γ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [Finset.sum_congr rfl fun γ _ => this γ, Finset.sum_const, Finset.card_univ]
    change (Fintype.card Γ : ℂ) • φ.1 (x * g) = _
    rw [Nat.cast_smul_eq_nsmul]
  have h2 : (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) ∘ₗ coindSum r σ =
      ∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * (x * g) := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    change (coindSum r σ φ).1 (x * g) = _
    rw [coindSum_apply]
    simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]
  rw [mul_comm, ← smul_eq_mul, ← map_smul, h1, LinearMap.trace_comp_comm', h2, map_sum]
  exact Finset.sum_congr rfl fun γ _ => trace_compLeft_funLeft _ _

end

end GlobalTheory.BadShare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelMemTwistedSpanFiniteStage
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem twKer_one_mem_aug_stage : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (U : Subgroup G) (N : ℕ → Set G), Monotone N →
    (∀ y ∈ U, ∃ m, y ∈ N m) → ∀ v ∈ twKer π U 1, ∃ m, v ∈ aug π (N m) (fun _ => 1) := by
  intro G V _ _ _ π U N hN hU v hv
  have mono : ∀ {a b : ℕ}, a ≤ b → aug π (N a) (fun _ => 1) ≤ aug π (N b) (fun _ => 1) := by
    intro a b h
    refine Submodule.span_mono ?_
    rintro x ⟨g, hg, w, rfl⟩
    exact ⟨g, hN h hg, w, rfl⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, w, rfl⟩ := hx
    obtain ⟨m, hm⟩ := hU n n.2
    exact ⟨m, Submodule.subset_span ⟨n, hm, w, by simp⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, add_mem (mono (le_max_left _ _) ha) (mono (le_max_right _ _) hb)⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, Submodule.smul_mem _ c ha⟩

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelTwoBlockUnipotentLeStages
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem twKer_unipB_le_of_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (P : Submodule ℂ V), twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1 ≤ P → (∀ u ∈ unipB k (Fin r), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (u, 1)) w - w ∈ P) → (∀ u ∈ unipB k (Fin t), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (1, u)) w - w ∈ P) → twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
  intro k _ _ _ _ r t V _ _ π P h0 h1 h2
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨u, hu⟩, w, rfl⟩
  set e := stdSum (rfl : r + t = r + t) with he
  obtain ⟨hl, hd⟩ := (mem_unipB k).1 hu
  have hp : u ∈ parab k (two e) := (mem_parab_two k).2 fun j i => hl _ _ (by
    rw [Fin.lt_def, he, stdSum_inl, stdSum_inr]; omega)
  obtain ⟨y, hy, hdec⟩ := exists_levi_mul_unip k (two e) ⟨u, hp⟩
  set a : GL (Fin r) k := leviProj k (two e) ⟨u, hp⟩ false with ha
  set b : GL (Fin t) k := leviProj k (two e) ⟨u, hp⟩ true with hb
  have hau : a ∈ unipB k (Fin r) := (mem_unipB k).2 ⟨fun i j hij => hl (e (.inl i)) (e (.inl j)) (by
    rw [Fin.lt_def, he, stdSum_inl, stdSum_inl]; exact hij), fun i => hd (e (.inl i))⟩
  have hbu : b ∈ unipB k (Fin t) := (mem_unipB k).2 ⟨fun i j hij => hl (e (.inr i)) (e (.inr j)) (by
    rw [Fin.lt_def, he, stdSum_inr, stdSum_inr]; exact Nat.add_lt_add_left hij r), fun i => hd (e (.inr i))⟩
  have hlev : leviEmb k (two e) (leviProj k (two e) ⟨u, hp⟩) = emb₂ k e (a, 1) * emb₂ k e (1, b) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    show _ = leviEmb k (two e) (leviTwo k _ _ (a, b))
    congr 1
    funext x
    cases x <;> rfl
  have hdec' : u = emb₂ k e (a, 1) * emb₂ k e (1, b) * y := by rw [← hlev]; exact hdec
  have h3 : π y w - w ∈ P := h0 (Submodule.subset_span ⟨⟨y, hy⟩, w, by simp⟩)
  have h4 := P.add_mem (P.add_mem (h1 a hau (π (emb₂ k e (1, b)) (π y w))) (h2 b hbu (π y w))) h3
  have h5 : π u w - w ∈ P := by
    rw [hdec', map_mul, map_mul]
    simpa using h4
  simpa using h5

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetSurvivalProductOfTwoGroups
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_mem_sup_twKer_prod : ∀ (G₁ G₂ V : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V), IsSmooth ρ → ∀ (U₁ : Subgroup G₁) (U₂ : Subgroup G₂) (J₁ : Set G₁) (J₂ : Set G₂) (θ₁ : G₁ → ℂ) (θ₂ : G₂ → ℂ), (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₁ W), IsSmooth σ → ∀ w ∈ twKer σ U₁ 1, IsEig σ J₁ θ₁ w → w = 0) → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₂ W), IsSmooth σ → ∀ w ∈ twKer σ U₂ 1, IsEig σ J₂ θ₂ w → w = 0) → ∀ v ∈ twKer (ρ.comp (MonoidHom.inl G₁ G₂)) U₁ 1 ⊔ twKer (ρ.comp (MonoidHom.inr G₁ G₂)) U₂ 1, IsEig (ρ.comp (MonoidHom.inl G₁ G₂)) J₁ θ₁ v → IsEig (ρ.comp (MonoidHom.inr G₁ G₂)) J₂ θ₂ v → v = 0 := by
  intro G₁ G₂ V _ _ _ _ _ _ _ _ ρ hρ U₁ U₂ J₁ J₂ θ₁ θ₂ h₁ h₂ v hv e₁ e₂
  have s₁ : IsSmooth (ρ.comp (MonoidHom.inl G₁ G₂)) := fun w =>
    (hρ w).preimage (f := fun g : G₁ => ((g, 1) : G₁ × G₂)) (by fun_prop)
  have s₂ : IsSmooth (ρ.comp (MonoidHom.inr G₁ G₂)) := fun w =>
    (hρ w).preimage (f := fun g : G₂ => ((1, g) : G₁ × G₂)) (by fun_prop)
  set ρ₁ : Representation ℂ G₁ V := ρ.comp (MonoidHom.inl G₁ G₂) with hρ₁
  set ρ₂ : Representation ℂ G₂ V := ρ.comp (MonoidHom.inr G₁ G₂) with hρ₂
  have comm : ∀ (a : G₁) (b : G₂) (w : V), ρ₁ a (ρ₂ b w) = ρ₂ b (ρ₁ a w) := by
    intro a b w
    change ρ (a, 1) (ρ (1, b) w) = ρ (1, b) (ρ (a, 1) w)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  set A : Submodule ℂ V := twKer ρ₂ U₂ 1 with hA
  have hst : ∀ g : G₁, A ≤ A.comap (ρ₁ g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, x, rfl⟩
    refine Submodule.subset_span ⟨n, ρ₁ g x, ?_⟩
    rw [map_sub, map_smul, comm]
  let σ : Representation ℂ G₁ (V ⧸ A) := Representation.quotient ρ₁ A hst
  have hσ : ∀ g x, σ g (A.mkQ x) = A.mkQ (ρ₁ g x) := fun g x => rfl
  have sσ : IsSmooth σ := by
    intro w
    obtain ⟨x, rfl⟩ := A.mkQ_surjective w
    let S : Subgroup G₁ :=
      { carrier := {g | σ g (A.mkQ x) = A.mkQ x}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have : (S : Set G₁) ∈ nhds (1 : G₁) := by
      refine Filter.mem_of_superset ((s₁ x).mem_nhds (by simp)) ?_
      intro g hg
      change σ g (A.mkQ x) = A.mkQ x
      rw [hσ, show ρ₁ g x = x from hg]
    exact S.isOpen_of_mem_nhds this
  have hmap : twKer ρ₁ U₁ 1 ≤ (twKer σ U₁ 1).comap A.mkQ := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, x, rfl⟩
    refine Submodule.subset_span ⟨n, A.mkQ x, ?_⟩
    rw [map_sub, map_smul, hσ]
  have hA0 : A ≤ (twKer σ U₁ 1).comap A.mkQ := by
    intro x hx
    have : A.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero A).2 hx
    rw [Submodule.mem_comap, this]
    exact zero_mem _
  have hv' : A.mkQ v ∈ twKer σ U₁ 1 := sup_le hmap hA0 hv
  have hz : A.mkQ v = 0 := h₁ _ σ sσ _ hv' (by
    intro h hh
    rw [hσ, e₁ h hh, map_smul])
  exact h₂ V ρ₂ s₂ v ((Submodule.Quotient.mk_eq_zero A).1 hz) e₂

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLaws
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.SlPLaws
open MvPolynomial

variable {R : Type} [CommRing R]

theorem slP_X (m : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    slP (R := R) m (X i) = (m i 0 : R) • X 0 + (m i 1 : R) • X 1 := by
  simp [slP]

theorem polySlash_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP (m * m') p = slP m' (slP m p) := by
  have h : (slP (R := R) (m * m')) = (slP m').comp (slP m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, slP_X, map_add, map_smul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    simp only [smul_add, add_smul, smul_smul, mul_comm]
    abel
  rw [h]; rfl

theorem polySlash_one' (p : MvPolynomial (Fin 2) R) : slP 1 p = p := by
  have h : (slP (R := R) 1) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [h]; rfl

theorem polySlash_isHomogeneous (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R)
    (hp : p.IsHomogeneous w) : (slP m p).IsHomogeneous w := by
  have := IsHomogeneous.aeval (τ := Fin 2) (S := R) (n := 1) hp (fun i => (m i 0 : R) • X 0 + (m i 1 : R) • X 1) (fun i => by
    apply IsHomogeneous.add
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 0).C_mul _
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 1).C_mul _)
  rw [one_mul] at this
  simpa [slP] using this

theorem eval_slP (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    eval u (slP m p) = eval (m.map (Int.castRingHom R) *ᵥ u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, eval_X]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem map_slP {S : Type} [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, map_X, map_add]
    simp [MvPolynomial.smul_eq_C_mul]

theorem polySlash_congr (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R)
    (h : ∀ i j, (m i j : R) = (m' i j : R)) : slP m p = slP m' p := by
  simp only [slP, h]

theorem polySlash_neg_one (w : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p.IsHomogeneous w) :
    slP (-1) p = (-1 : R) ^ w • p := by
  have e : (slP (R := R) (-1)) = aeval fun i => (-1 : R) • X i := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [e]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hw := hp (mem_support_iff.mp hv)
  rw [aeval_monomial]
  simp only [smul_pow, Finsupp.prod_pow]
  have hw' : v 0 + v 1 = w := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]; simp
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, ← hw']
  simp only [smul_eq_C_mul, algebraMap_eq, pow_add, map_mul, map_pow, map_neg, map_one]
  ring

end GlobalTheory.KZ.SlPLaws

namespace GlobalTheory.KZ

theorem polySlash_laws : ∀ (R : Type) [CommRing R], (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), slP (m * m') p = slP m' (slP m p)) ∧ (∀ p : MvPolynomial (Fin 2) R, slP 1 p = p) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → (slP m p).IsHomogeneous w) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R), MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p)) ∧ (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), (∀ i j, (m i j : R) = (m' i j : R)) → slP m p = slP m' p) ∧ (∀ (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → slP (-1) p = (-1 : R) ^ w • p) := by
  intro R _
  exact ⟨SlPLaws.polySlash_mul, SlPLaws.polySlash_one', SlPLaws.polySlash_isHomogeneous, SlPLaws.eval_slP, fun S _ f => SlPLaws.map_slP f,
    fun m m' p h => SlPLaws.polySlash_congr m m' p h, fun w p hp => SlPLaws.polySlash_neg_one w p hp⟩

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOneStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_tower_zeta_sub_one : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), v (p : Ω) < 1 → ∀ n : ℕ, 1 ≤ n → v (T.ζ n - 1) < 1 ∧ v (p : Ω) ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by
  first | exact @GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one | exact GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one | (intros; apply GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.XMulMemSpanOfColemanLevelsStatement
section
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_mul_mem_span_of_colemanLevels : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime], IsDomain R → Prime (p : R) → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (h : PowerSeries R) (k c : ℕ), (∀ r, 1 ≤ r → r ≤ k → ∃ y : PowerSeries R, ev R p r h = ev R p r ((p : PowerSeries R) ^ c * y)) → ∀ j, j ≤ k → j ≤ c → X * h ∈ Ideal.span {(p : PowerSeries R) ^ (c - j), (1 + X) ^ (p ^ j) - 1} := by
  first | exact @GlobalTheory.Col.X_mul_mem_span_of_levels | exact GlobalTheory.Col.X_mul_mem_span_of_levels | (intros; apply GlobalTheory.Col.X_mul_mem_span_of_levels <;> assumption)
end

