import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacter
section
open Matrix

noncomputable section
namespace GlobalTheory.SvNAnyChar

def scaleSnd {k : Type} [Field k] {κ : Type} (c : k) :
    (κ → k) × (κ → k) →+ (κ → k) × (κ → k) where
  toFun w := (w.1, c • w.2)
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem scaleSnd_fst {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).1 = w.1 := rfl

@[simp] theorem scaleSnd_snd {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).2 = c • w.2 := rfl

theorem schr_mulShift_scaleSnd {k : Type} [Field k] [Invertible (2 : k)] {κ : Type} [Fintype κ]
    (ψ : AddChar k ℂ) {c : k} (hc : c ≠ 0) (w : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    GlobalTheory.WeilM.schr (ψ.mulShift c) (scaleSnd c⁻¹ w) φ = GlobalTheory.WeilM.schr ψ w φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, scaleSnd_fst, scaleSnd_snd, AddChar.mulShift_apply, dotProduct_smul,
    smul_eq_mul]
  congr 2
  rw [mul_add, mul_left_comm c (⅟2), mul_inv_cancel_left₀ hc, mul_inv_cancel_left₀ hc]

theorem stoneVonNeumann_any_char :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  intro k _ _ _ _ _ _ κ _ n d ψ0 hψ hne wT wM hT hM hTM hsurj
  obtain ⟨c, hc, hcond⟩ := GlobalTheory.CondRescale.exists_rescale_conductor_integers ψ0 hψ hne
  have hψ1 : Continuous (ψ0.mulShift c) := by
    have : (ψ0.mulShift c : k → ℂ) = fun x => ψ0 (c * x) := by
      funext x
      exact AddChar.mulShift_apply
    rw [this]
    exact hψ.comp (continuous_const.mul continuous_id)
  let S : Matrix (Fin n) (Fin d) k →+ Matrix (Fin n) (Fin d) k :=
    { toFun := fun z => c • z
      map_zero' := smul_zero c
      map_add' := smul_add c }
  have hS : ∀ z, S z = c • z := fun _ => rfl
  have hsum : ∀ (a : k) (Y z : Matrix (Fin n) (Fin d) k),
      ∑ i, ∑ j, Y i j * (a • z) i j = a * ∑ i, ∑ j, Y i j * z i j := by
    intro a Y z
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨ι, hbij, h1, h2⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians (κ := κ) (n := n) (d := d) (ψ0.mulShift c) hψ1
    (fun x => by simpa only [AddChar.mulShift_apply] using hcond x)
    ((scaleSnd c⁻¹).comp wT) ((scaleSnd c⁻¹).comp (wM.comp S))
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hT, mul_zero])
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hM, mul_zero])
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hTM, hS, hsum, inv_mul_cancel_left₀ hc])
    (fun w => by
      obtain ⟨Y, z, h⟩ := hsurj (scaleSnd c w)
      refine ⟨Y, c⁻¹ • z, ?_⟩
      simp only [AddMonoidHom.comp_apply]
      rw [hS, smul_inv_smul₀ hc, ← map_add, h]
      exact Prod.ext rfl (inv_smul_smul₀ hc _))
  refine ⟨ι, hbij, fun Y φ hφ => ?_, fun z φ hφ => ?_⟩
  · have := h1 Y φ hφ
    rwa [AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc] at this
  · have := h2 (c⁻¹ • z) φ hφ
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc, hS,
      smul_inv_smul₀ hc] at this
    rw [this]
    funext Y'
    rw [AddChar.mulShift_apply, hsum, mul_inv_cancel_left₀ hc]

end GlobalTheory.SvNAnyChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
section
noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F]

theorem hasOp_of_symplectic (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (ha : aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0) : HasOp ψ a :=
  GlobalTheory.T.symplecticGroup_generated_levi_lowerUnipotent_weyl F κ (HasOp ψ) (fun _ _ => HasOp.mul) (GlobalTheory.T.hasRationalWeilOperator_leviBlock F ψ κ) (GlobalTheory.T.lowerUnipotent_hasRationalWeilOperator_quadraticChar F ψ hψ κ) (GlobalTheory.T.weylElement_hasRationalWeilOperator_adelicFourier F hF ψ hψ κ) a ha

section Pure

variable {κ : Type} [Fintype κ]

theorem pure_mem (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F κ :=
  Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ.1 hφ.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ.1 hφ.2⟩, rfl⟩

theorem schA_le {N : Submodule ℂ ((κ → AF F) → ℂ)} (h : ∀ f φ, IsFam φ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N) : schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ ⟨hφ, hs⟩

theorem IsFam.finite {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v => φ v fun i => evFin F v (x i)).Finite := by
  have h : ∀ᶠ v in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F := eventually_all.2 fun i => (x i).2.2
  refine (eventually_cofinite.1 ?_)
  filter_upwards [h, hφ.2] with v h1 h2
  rw [h2, ind, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h1)]
  rfl

theorem pure_smul (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (m : Pl F → ℂ) (h0 : ∀ v, m v ≠ 0)
    (h1 : ∀ᶠ v in cofinite, m v = 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ᶠ v, m v) • f) (fun v => (m v)⁻¹ • φ v) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  have hm : (Function.mulSupport m).Finite := eventually_cofinite.1 h1
  have hm' : (Function.mulSupport fun v => (m v)⁻¹).Finite := hm.subset fun v hv h => hv (by simp only [h, inv_one])
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  rw [finprod_mul_distrib hm' (hφ.finite x)]
  have : (∏ᶠ v, m v) * ∏ᶠ v, (m v)⁻¹ = 1 := by
    rw [← finprod_mul_distrib hm hm']
    exact finprod_eq_one_of_forall_eq_one fun v => mul_inv_cancel₀ (h0 v)
  linear_combination (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) * this

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) :
    ((κ → R) → ℂ) →ₗ[ℂ] (κ → R) → ℂ where
  toFun := schr ψ w
  map_add' φ φ' := funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' a φ := funext fun x => by simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

variable {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ}
  {ei : SInf F κ →L[ℂ] SInf F κ} {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ}

theorem IsOp.maps (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ := fun _ hΦ =>
  schA_le (N := (schA F κ).comap e) (fun f φ hφ => by
    rw [Submodule.mem_comap, (h.2.2.2.2.2 f φ hφ).1]
    exact pure_mem _ (h.isFam hφ)) hΦ

theorem IsOp.Heisenberg₂ (h : IsOp ψ a e c ei ev) (w : (κ → AF F) × (κ → AF F)) :
    ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (act (a.map (algebraMap F (AF F))) w) (e Φ) := fun _ hΦ =>
  schA_le (N := LinearMap.eqLocus (e ∘ₗ schrL ψ w) (schrL ψ (act (a.map (algebraMap F (AF F))) w) ∘ₗ e))
    (fun f φ hφ => (h.2.2.2.2.2 f φ hφ).2.1 w) hΦ

theorem IsOp.theta (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := fun _ hΦ =>
  (schA_le (N := {
      carrier := {Φ | Φ ∈ schA F κ ∧ thetaSum F (e Φ) = c * thetaSum F Φ}
      zero_mem' := ⟨zero_mem _, by simp [thetaSum]⟩
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        rw [map_add, thetaSum_add F (h.maps _ hx.1) (h.maps _ hy.1), thetaSum_add F hx.1 hy.1, hx.2, hy.2, mul_add]⟩
      smul_mem' := fun r x hx => ⟨Submodule.smul_mem _ r hx.1, by
        rw [map_smul, thetaSum_smul, thetaSum_smul, hx.2, mul_left_comm]⟩ })
    (fun f φ hφ => ⟨pure_mem f hφ, (h.2.2.2.2.2 f φ hφ).2.2⟩) hΦ).2

theorem IsOp.bijOn (hψ : IsStd ψ) (h : IsOp ψ a e c ei ev) : Set.BijOn e (schA F κ : Set _) (schA F κ : Set _) := by
  classical
  refine ⟨h.maps, fun Φ hΦ Φ' hΦ' he => ?_, ?_⟩
  · have hd : Φ - Φ' ∈ schA F κ := sub_mem hΦ hΦ'
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero F ψ hψ κ _ hd fun w => ?_)
    have h1 := h.theta _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w _ hd)
    rw [h.Heisenberg₂ w _ hd, map_sub, he, sub_self, show schr ψ _ (0 : (κ → AF F) → ℂ) = 0 from (schrL ψ _).map_zero] at h1
    exact (mul_eq_zero.1 (h1.symm.trans (by simp [thetaSum]))).resolve_left h.1
  · refine schA_le (N := (schA F κ).map e) fun g φ' hφ' => ?_
    obtain ⟨f, rfl⟩ := h.2.1 g
    have key : ∀ v, ∃ p ∈ SB (κ → Fv F v), ev v p = φ' v ∧ (φ' v = ind κ v → ev v (ind κ v) = ind κ v → p = ind κ v) := by
      intro v
      by_cases hv : φ' v = ind κ v ∧ ev v (ind κ v) = ind κ v
      · exact ⟨ind κ v, hv.1 ▸ hφ'.1 v, hv.2.trans hv.1.symm, fun _ _ => rfl⟩
      · obtain ⟨p, hp, hp'⟩ := (h.2.2.1 v).surjOn (hφ'.1 v)
        exact ⟨p, hp, hp', fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
    choose φ h1 h2 h3 using key
    have hφ : IsFam φ := ⟨h1, by filter_upwards [hφ'.2, h.2.2.2.2.1] with v p q using h3 v p q⟩
    exact ⟨_, pure_mem f hφ, by rw [(h.2.2.2.2.2 f φ hφ).1]; simp only [h2]⟩

end Pure

section Vac

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem schr_of_acts (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v)
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB _) {χ : ℂ} (h : Acts (evFin F v) (M.co.rho ψ γ) φ (χ • φ)) :
    schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ = χ • φ := by
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v φ hφ
  funext ξ
  have := GlobalTheory.LatVac.heis_at_local_identity v M.co ψ γ φ χ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) h r hr x₀ hx₀ ξ
  rw [schr, invOf_eq_inv]
  exact this

theorem vac_line (B : Base F E) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (M : Model σ X W) (v : Pl F) {φ φ' : (Fin n × Fin d → Fv F v) → ℂ} (h : M.IsVac B.ψ v φ) (h' : M.IsVac B.ψ v φ') :
    ∃ m : ℂ, φ' = m • φ := by
  classical
  obtain ⟨hφ, hφ0, θ, hθ, hA⟩ := h
  obtain ⟨hφ', -, θ', hθ', hA'⟩ := h'
  have hAt := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  let χ : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin n × Fin d → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • f)) →
      ∀ l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l := AddSubgroup.mem_map.mp hl
    have key := congrFun (schr_of_acts M B.ψ h.choose_spec.1 hf (hA _ h.choose_spec.1)) ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2, schr, invOf_eq_inv] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat hW.lat
  have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ hAt (GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace F E σ B n d X W r s r' s' hB hX hW v)
  have hfill := GlobalTheory.T.self_dual_lattice_invariant_vector F v _ (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (fun _ => GlobalTheory.StdCharFromIsStd.norm_psi hB.std _) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) _ c hc0 hsd
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  refine GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) _ χ φ φ' (loc φ hφ hA) (loc φ' hφ' fun γ hγ => ?_) hφ0 hfill
  rw [GlobalTheory.T.vacuum_eigenvalue_theta_independent F E σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ]
  exact hA' γ hγ

theorem IsOp.isVac {ψ : AddChar (AF F) ℂ} {a e c ei ev} (h : IsOp (κ := Fin n × Fin d) ψ a e c ei ev) (M M₁ : Model σ X W)
    (hco : ∀ u, M₁.co.e u = act (a.map (algebraMap F (AF F))) (M.co.e u)) (v : Pl F) {φ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : M.IsVac ψ v φ) : M₁.IsVac ψ v (ev v φ) := by
  obtain ⟨h1, h0, θ, hθ, hA⟩ := hφ
  refine ⟨(h.2.2.1 v).mapsTo h1, fun h2 => h0 ((h.2.2.1 v).injOn h1 (zero_mem _) (h2.trans (map_zero _).symm)), θ, hθ,
    fun γ hγ => ?_⟩
  have e1 : GlobalTheory.LatVac.locCo M₁.co v γ = act (a.map (algebraMap F (Fv F v))) (GlobalTheory.LatVac.locCo M.co v γ) := by
    have e2 : ∀ k, evFin F v ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e γ).1 (M.co.e γ).2) k) =
        (a.map (algebraMap F (Fv F v)) *ᵥ Sum.elim (GlobalTheory.LatVac.locCo M.co v γ).1 (GlobalTheory.LatVac.locCo M.co v γ).2) k := fun k => by
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases j <;> rfl
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show evFin F v ((M₁.co.e γ).1 k) = _
      rw [hco]; exact e2 _
    · show evFin F v ((M₁.co.e γ).2 k) = _
      rw [hco]; exact e2 _
  have e3 := GlobalTheory.VacBridge.rho_acts_locCo M₁.co ψ v γ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) (ev v φ)
  rwa [e1, ← h.2.2.2.1 v _ φ h1, schr_of_acts M ψ hγ h1 (hA γ hγ), map_smul] at e3

end Vac

theorem exists_intertwiner : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → (∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr)) → ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ), c ≠ 0 ∧ IsEv B M M₁ 1 1 ∅ e ∧ Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c * thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M M₁ r s r' s' hB hX hW hM hM₁ a ha hco
  obtain ⟨e, c, ei, ev, h⟩ := hasOp_of_symplectic hB.cm.1 hB.std a ha
  have key : ∀ v, ∃ m : ℂ, m ≠ 0 ∧ ev v (M.vac v) = m • M₁.vac v ∧ (ev v (M.vac v) = M₁.vac v → m = 1) := fun v => by
    by_cases hv : ev v (M.vac v) = M₁.vac v
    · exact ⟨1, one_ne_zero, by rw [hv, one_smul], fun _ => rfl⟩
    · have h1 := h.isVac M M₁ hco v (hM.vac v)
      obtain ⟨m, hm⟩ := vac_line B hB hX hW M₁ v (hM₁.vac v) h1
      exact ⟨m, fun h0 => h1.2.1 (by rw [hm, h0, zero_smul]), hm, fun h2 => absurd h2 hv⟩
  choose m hm0 hm hm1 using key
  have hmc : ∀ᶠ v in cofinite, m v = 1 := by
    filter_upwards [hM.std, hM₁.std, h.2.2.2.2.1] with v h1 h2 h3
    exact hm1 v (by rw [h1, h2]; exact h3)
  have hP : (∏ᶠ v, m v) ≠ 0 := finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hm0
  refine ⟨e, c, h.1, ⟨h.maps, fun z Φ hΦ => ?_, fun u hu => absurd hu (Set.notMem_empty u),
    (∏ᶠ v, m v) • ei, fun v => (m v)⁻¹ • ev v, fun h0 => ?_, fun v => ⟨?_, ?_⟩, fun f φ h1 h2 => ?_⟩, h.bijOn hB.std, h.theta⟩
  · have h1 : ∀ k : ℕ, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := fun k => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Darboux.rho, Darboux.rho, hco]
    exact h.Heisenberg₂ _ Φ hΦ
  · have h1 : ei = 0 := (smul_eq_zero.1 h0).resolve_left hP
    obtain ⟨Φ, hΦ, hΦ0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (Fin n × Fin d)
    have h2 : schA F (Fin n × Fin d) ≤ ⊥ := schA_le fun g φ _ => by
      obtain ⟨f, rfl⟩ := h.2.1 g
      rw [h1, Submodule.mem_bot]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    exact hΦ0 (by rw [(Submodule.mem_bot ℂ).1 (h2 hΦ)]; rfl)
  · rw [LinearMap.smul_apply, hm, smul_smul, inv_mul_cancel₀ (hm0 v), one_smul]
  · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hm0 v))]
    exact SetLike.coe_injective ((Submodule.map_coe _ _).trans (h.2.2.1 v).image_eq)
  · have hφ : IsFam φ := ⟨h1, by filter_upwards [h2, hM.std] with v p q using p.trans q⟩
    rw [(h.2.2.2.2.2 f φ hφ).1, ← pure_smul (ei f) (h.isFam hφ) m hm0 hmc]
    rfl

end GlobalTheory.RatWeilOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHermitianFormInertPointEqLocalForm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.InertTens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem quadruple_sum_eq_trace_transpose_mul {L : Type} [CommRing L] {m n : ℕ} (P : Matrix (Fin m) (Fin n) L) (J : Matrix (Fin m) (Fin m) L)
    (K : Matrix (Fin n) (Fin n) L) (Q : Matrix (Fin m) (Fin n) L) :
    ∑ i, ∑ j, ∑ k, ∑ l, P i j * J i k * K j l * Q k l = (Pᵀ * J * Q * Kᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem trace_orth {L : Type} [Field L] (σL : L →+* L) {m n : ℕ} (J : Matrix (Fin m) (Fin m) L) (K : Matrix (Fin n) (Fin n) L)
    (A : Matrix (Fin m) (Fin m) L) (Bm : Matrix (Fin n) (Fin n) L) (δ : L)
    (hA : Aᵀ * J * A.map σL = 1) (hB : Bmᵀ * K * Bm.map σL = δ • 1) (x y : Matrix (Fin n) (Fin m) L) :
    ((A * xᵀ * Bmᵀ)ᵀ * J * (A * yᵀ * Bmᵀ).map σL * Kᵀ).trace = δ * ((y.map σL)ᵀ * x).trace := by
  have e1 : (A * yᵀ * Bmᵀ).map σL = A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
  have e2 : (Bm.map σL)ᵀ * Kᵀ * Bm = δ • 1 := by
    have := congrArg Matrix.transpose hB
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [e1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have e3 : Bm * (x * Aᵀ) * J * (A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ) * Kᵀ
      = Bm * (x * (Aᵀ * J * A.map σL) * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ)) := by
    simp only [Matrix.mul_assoc]
  rw [e3, hA, Matrix.trace_mul_comm, Matrix.mul_one]
  have e4 : x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ) * Bm = x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ * Bm) := by
    simp only [Matrix.mul_assoc]
  rw [e4, e2, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem hTens_kap (σ : E →ₐ[F] E) {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) {σL : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h σL)
    {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (x y : Matrix (Fin n) (Fin m) (w.adicCompletion E)) :
    hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
      ptAt hw h (∑ i, ∑ j, ∑ k, ∑ l, (A * xᵀ * Bmᵀ) i j * JA.map (algebraMap E (w.adicCompletion E)) i k *
        JB.map (algebraMap E (w.adicCompletion E)) j l * (A * yᵀ * Bmᵀ).map σL k l) := by
  have hr : ∀ (a : E) (z : w.adicCompletion E),
      ptAt hw h z * inclR (F := F) (AF F) a = ptAt hw h (z * algebraMap E (w.adicCompletion E) a) := by
    intro a z
    rw [mul_comm, inclR_mul_ptAt, mul_comm]
  simp only [hTens, incM, kap_apply, Matrix.map_apply, cA_ptAt hw h σ hc, hr, ← map_mul, map_sum]

end GlobalTheory.InertTens

namespace GlobalTheory.InertTens

theorem hTens_kap_eq_locH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin m) (Fin m) (w.adicCompletion E))
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      Aᵀ * JA.map (algebraMap E (w.adicCompletion E)) * A.map σL = 1 →
      Bmᵀ * JB.map (algebraMap E (w.adicCompletion E)) * Bm.map σL = δ • 1 →
      ∀ x y, hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
        ptAt hw h (GlobalTheory.Hk3.locH σL δ (1 : GL (Fin m) (w.adicCompletion E)) (1 : GL (Fin n) (w.adicCompletion E)) x y) := by
  intro F E _ _ _ _ _ σ v w hw h σL hc m n JA JB A Bm δ hA hB x y
  rw [hTens_kap σ hw h hc, quadruple_sum_eq_trace_transpose_mul, trace_orth σL _ _ A Bm δ hA hB x y]
  congr 1
  simp [GlobalTheory.Hk3.locH]

end GlobalTheory.InertTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFiringRowAtConcreteLifts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFireAssembly

theorem thetaFireRow_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → R.ExAt → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ IL : RecTie.LiftIds (RecTie.toLiftReal R F tupT hm hTop hinj), RecTie.ThetaFireRow (RecTie.toLiftReal R F tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj h e hv IL
  have hP : R.IsThP := RealDat.thP_of_weak h.thP e
  refine ⟨fun μ _ i => GlobalTheory.ThetaPRead.isThetaP_toLiftReal R F tupT hm hTop hinj hP.thF μ i, ?_, ?_⟩
  · exact GlobalTheory.T.thetaAdjoint_at_lift_eq_lowestKType_restriction R F tupT hm hTop hinj h.lev h.grp h.models hP hv IL
  · exact GlobalTheory.LiftResInj.resInjL_toLiftReal R F tupT hm hTop hinj h.models.inf

end GlobalTheory.ThetaFireAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledCoordsBoxProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_doubledCoords_boxProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) =>
            GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) *
              star (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => star (φ₂ x)) (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)) := by
  first | exact @GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun | exact GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun | (intros; apply GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformHasLevelCmExtensionStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_hasLevel_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 →
              Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) =
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ := by
  first | exact @GlobalTheory.ThetaLevelCM.thetaTr_level | exact GlobalTheory.ThetaLevelCM.thetaTr_level | (intros; apply GlobalTheory.ThetaLevelCM.thetaTr_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleSquareSplitPlaceCharacterEqLocalGridStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleSquare_splitPlace_character_eq_localGrid : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil)
    (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ (w : Pl D.host.E) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    splitPrime τ = w →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ = ((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α τ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β τ := by
  first | exact @GlobalTheory.PureMatch.chrW_triple_split_nu | exact GlobalTheory.PureMatch.chrW_triple_split_nu | (intros; apply GlobalTheory.PureMatch.chrW_triple_split_nu <;> assumption)
end

