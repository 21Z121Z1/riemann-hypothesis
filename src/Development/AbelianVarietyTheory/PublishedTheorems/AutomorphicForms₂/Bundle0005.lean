import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDefinite
section
open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta

noncomputable section

namespace GlobalTheory.Published.DSExistsRecordModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem goodPar_of_signs (n : ℕ) (ε : Fin n → Bool) :
    ∃ S : SPar, GoodPar n (Finset.univ.filter fun a => ε a = true).card
      (Finset.univ.filter fun a => ε a = false).card S := by
  refine ⟨Finset.univ.image fun a : Fin n => ((((n : ℚ) - 1) / 2 - ((a : ℕ) : ℚ)), ε a), DSExistsModel.lamDet n 0, ε,
    ⟨(DSExistsModel.lamDet_hc n 0).1, fun a => ((n : ℚ) - 1) / 2 - ((a : ℕ) : ℚ), fun a => ?_, rfl⟩,
    DSExistsModel.lamDet_hc n 0, rfl, rfl⟩
  simp [DSExistsModel.lamDet, Formalism.QuantumDeterminants.rhoStd]

theorem const_of_card {n : ℕ} (ε : Fin n → Bool)
    (h : (Finset.univ.filter fun a => ε a = true).card = 0 ∨ (Finset.univ.filter fun a => ε a = false).card = 0) :
    ∃ b, ε = fun _ => b := by
  rcases h with h | h
  · refine ⟨false, funext fun a => ?_⟩
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    simpa using h (Finset.mem_univ a)
  · refine ⟨true, funext fun a => ?_⟩
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    simpa using h (Finset.mem_univ a)

theorem dsExists_of_definite (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar)
    (hd : ∀ τ, (V.sig (tauE D τ)).1 = 0 ∨ (V.sig (tauE D τ)).2 = 0) : Formalism.IndefR.Mult.DSExists V S := by
  intro hV hS
  choose lam ε hE hP hp hq using hS
  have key : ∀ τ, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)), IsDS (ε τ) (lam τ) σ := by
    intro τ
    obtain ⟨b, hb⟩ := const_of_card (ε τ) (by rw [hp, hq]; exact hd τ)
    rw [hb]
    exact GlobalTheory.CompactDS.exists_isDS_const _ b _ (hP τ)
  choose H i1 i2 σ hσ using key
  choose A hA hG using fun τ => exists_frame_of_hasSignature (hV (tauE D τ)) (ε τ) (hp τ) (hq τ)
  exact ⟨@Formalism.IndefR.Mult.DSModel.mk D V S H i1 i2 σ lam ε A hE hσ hA hG⟩

theorem iff_indefinite : DiscreteSeriesExists ↔
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), (∃ a b, ε a ≠ ε b) → Formalism.QuantumDeterminants.IsHCParam lam →
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ := by
  rw [discreteSeriesExists_iff]
  refine ⟨fun h n ε lam _ hl => h n ε lam hl, fun h n ε lam hl => ?_⟩
  by_cases hc : ∃ a b, ε a ≠ ε b
  · exact h n ε lam hc hl
  · push Not at hc
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact DSExistsModel.holds_rank_le_one 0 (by norm_num) ε lam hl
    · have : ε = fun _ => ε ⟨0, hn⟩ := funext fun a => hc _ _
      rw [this]
      exact GlobalTheory.CompactDS.exists_isDS_const _ _ _ hl

theorem isHCParam_of_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S)
    (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (M.lam τ) :=
  ⟨(M.enum τ).1, DSExistsModel.integral_of_isDS (M.ε τ) (M.lam τ) (M.σ τ) (M.ds τ)⟩

theorem not_isDS_singular {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin 2) (Fin 2) ℂ → (H →L[ℂ] H)) : ¬ IsDS (fun _ => true) (fun _ => 1 / 2) σ := by
  rintro ⟨-, -, ⟨⟨h1, hm⟩, hn, -⟩, -, -, ⟨S, -, hK, -, ⟨v, hvS, hv, hw⟩, hc⟩, -⟩
  have hL : Formalism.QuantumDeterminants.lowK (fun _ : Fin 2 => true) (fun _ => 1 / 2) = ![0, 1] := by
    funext a
    rw [GlobalTheory.DefiniteCheck.lowK_const]
    fin_cases a <;> simp <;> norm_num
  rw [hL] at hw hc
  have hJ : Formalism.REAL.Jm (fun _ : Fin 2 => true) = 1 := by simp [Formalism.REAL.Jm]
  have hKU : ∀ g ∈ Formalism.REAL.Kset (fun _ : Fin 2 => true), g ∈ UJset (fun _ : Fin 2 => true) := by
    intro g hg
    have := (Matrix.mem_unitaryGroup_iff').1 hg.1
    show gᴴ * _ * g = _
    rw [hJ, Matrix.mul_one]; exact this
  let w : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  have hwK : w ∈ Formalism.REAL.Kset (fun _ : Fin 2 => true) := by
    refine ⟨?_, by rw [hJ]; simp⟩
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j; fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two]
  have hne : σ w v ≠ 0 := by
    intro h0
    have := hn w (hKU w hwK) v
    rw [h0, norm_zero] at this
    exact hv (norm_eq_zero.1 this.symm)
  have hwt : IsWtOn (Formalism.REAL.Kset (fun _ : Fin 2 => true)) σ ![1, 0] (σ w v) := by
    intro θ hθ
    have h2 := hw ![θ 1, θ 0] (DSExistsModel.diag_mem _ _)
    have e : Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * w =
        w * Matrix.diagonal (fun a => Complex.exp (((![θ 1, θ 0] : Fin 2 → ℝ) a : ℂ) * Complex.I)) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    have a1 := congrArg (fun T : H →L[ℂ] H => T v) (hm _ (hKU _ hθ) w (hKU w hwK))
    have a2 := congrArg (fun T : H →L[ℂ] H => T v) (hm w (hKU w hwK) _ (hKU _ (DSExistsModel.diag_mem _ ![θ 1, θ 0])))
    simp only [ContinuousLinearMap.comp_apply] at a1 a2
    rw [← a1, e, a2, h2, map_smul]
    simp [Fin.sum_univ_two]
  obtain ⟨c, hc1, hc2⟩ := hc _ _ (hK w hwK v hvS) hne hwt
  have h10 : c 1 0 = 0 := by
    by_contra h; exact absurd (hc1 1 0 h).1 (by decide)
  have := congrFun hc2 0
  simp [Fin.sum_univ_two, Formalism.REAL.root, h10] at this
  have h0 : (0 : ℝ) ≤ c 0 1 := Nat.cast_nonneg _
  linarith

end GlobalTheory.Published.DSExistsRecordModel
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.Published

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace AutFin

def coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) :
    Submodule ℂ (K → ℂ) :=
  Submodule.span ℂ {f | ∃ (ℓ : Module.Dual ℂ W) (w : W), f = fun k => ℓ (ρ k w)}

def IsContRep {K W : Type} [Group K] [TopologicalSpace K] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) : Prop :=
  ∀ (ℓ : Module.Dual ℂ W) (w : W), Continuous fun k => ℓ (ρ k w)

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

def IsFrameFam (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, IsUnit (fr τ) ∧ (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ

def kAt (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : Formalism.REAL.KG e) :
    GA D V :=
  atTau θ V τ (P⁻¹ * Formalism.REAL.toMK k * P)

def HasTypeAt (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ : GA D V → ℂ) : Prop :=
  ∀ x : GA D V, (fun k => φ (x * kAt θ V τ e P k)) ∈ coeffSpan ρ

def forms (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)]
    [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) :
    Set (GA D V → ℂ) :=
  {φ | IsAutFunSm θ V φ ∧ (∀ u ∈ U, u ∈ GfC V → ∀ g, φ (g * u) = φ g) ∧
    (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) ∧ ∀ τ k, gelf θ V τ k φ = c τ k • φ}

end AutFin

open AutFin in

def HarishChandraFinite : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) →
  ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsFrameFam V ε fr →
  ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) →
  ∀ c : D.what₂.Tau → ℕ → ℂ,
    FiniteDimensional ℂ (Submodule.span ℂ (forms θ V U ε fr ρ c))

namespace AutFin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem conj_mem_UH {n : ℕ} {e : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm e * P = G) (k : Formalism.REAL.KG e) :
    P⁻¹ * Formalism.REAL.toMK k * P ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk : (Formalism.REAL.toMK k)ᴴ * Formalism.REAL.Jm e * Formalism.REAL.toMK k = Formalism.REAL.Jm e := (k : Formalism.REAL.UJ e).2
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
  change (P⁻¹ * Formalism.REAL.toMK k * P)ᴴ * G * (P⁻¹ * Formalism.REAL.toMK k * P) = G
  calc (P⁻¹ * Formalism.REAL.toMK k * P)ᴴ * G * (P⁻¹ * Formalism.REAL.toMK k * P)
      = Pᴴ * ((Formalism.REAL.toMK k)ᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm e * (P * P⁻¹) * Formalism.REAL.toMK k) * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk, h]

open Classical in

theorem isAtTau_kAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    (k : Formalism.REAL.KG e) : IsAtTau θ V τ (P⁻¹ * Formalism.REAL.toMK k * P) (kAt θ V τ e P k) := by
  obtain ⟨g, hg, h1⟩ := ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.1
    (Function.update (fun _ => 1) τ (P⁻¹ * Formalism.REAL.toMK k * P)) (fun τ' => by
      by_cases c : τ' = τ
      · subst c; rw [Function.update_self]; exact conj_mem_UH hP h k
      · rw [Function.update_of_ne c]
        change (1 : Matrix _ _ ℂ)ᴴ * _ * 1 = _
        rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one])
  have hex : ∃ x, IsAtTau θ V τ (P⁻¹ * Formalism.REAL.toMK k * P) x :=
    ⟨g, hg, by rw [h1, Function.update_self], fun τ' c => by rw [h1, Function.update_of_ne c]⟩
  rw [kAt, atTau, dif_pos hex]
  exact hex.choose_spec

theorem hasTypeAt_of_map (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (T : W →ₗ[ℂ] (GA D V → ℂ))
    (hT : ∀ k w, T (ρ k w) = rTr V (kAt θ V τ e P k) (T w)) (w : W) : HasTypeAt θ V τ e P ρ (T w) := fun x =>
  Submodule.subset_span ⟨(LinearMap.proj x).comp T, w, funext fun k => (congrFun (hT k w) x).symm⟩

theorem exists_isFrameFam (hV : V.SigOK) : ∃ ε fr, IsFrameFam V ε fr := by
  have key : ∀ τ, ∃ (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsUnit P ∧ Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ := by
    intro τ
    obtain ⟨hpq, ⟨A, hA⟩, hB⟩ := GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D τ))
    obtain ⟨B, hAB, -⟩ := hB A hA
    let s := (finSumFinEquiv.trans (finCongr hpq)).symm
    have hJ : Formalism.REAL.Jm (fun i => (s i).isLeft) = (Formalism.UG.Jpq _ _).submatrix s s := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Formalism.REAL.Jm, diagonal_apply_eq, submatrix_apply]
        rcases s i with a | a <;> simp [Formalism.UG.Jpq]
      · have hs : s i ≠ s j := fun h => hij (s.injective h)
        rw [Formalism.REAL.Jm, diagonal_apply_ne _ hij, submatrix_apply]
        revert hs
        rcases s i with a | a <;> rcases s j with b | b <;> simp +contextual [Formalism.UG.Jpq, Matrix.one_apply]
    refine ⟨fun i => (s i).isLeft, A.submatrix s id, ?_, ?_⟩
    · refine IsUnit.of_mul_eq_one (B.submatrix id s) ?_
      rw [← submatrix_mul A B s id s Function.bijective_id, hAB, submatrix_one_equiv]
    · rw [hJ, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hA]
      rfl
  choose ε fr h using key
  exact ⟨ε, fr, h⟩

theorem const_mem_forms (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (a : ℂ) :
    (fun _ => a) ∈ forms θ V U ε fr (fun τ => Representation.trivial ℂ (Formalism.REAL.KG (ε τ)) ℂ) (fun _ _ => 0) := by
  refine ⟨isAutFunSm_const θ V a, fun _ _ _ _ => rfl, fun τ x => Submodule.subset_span ⟨LinearMap.id, a, rfl⟩,
    fun τ k => ?_⟩
  rw [zero_smul, gelf]
  refine Finset.sum_eq_zero fun idx _ => ?_
  rw [List.ofFn_succ, List.foldr_cons]
  obtain ⟨b, hb⟩ := foldr_const V (List.ofFn fun i : Fin k =>
    RderC θ V τ (Matrix.single (idx i.succ) (idx (i.succ + 1)) 1)) (fun f hf c₀ => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      exact ⟨0, RderC_const θ V τ _ c₀⟩) a
  rw [hb, RderC_const]
  rfl

theorem isContRep_trivial {K : Type} [Group K] [TopologicalSpace K] : IsContRep (Representation.trivial ℂ K ℂ) :=
  fun ℓ w => (continuous_const : Continuous fun _ : K => ℓ w)

end AutFin

end GlobalTheory.Published

end
end

