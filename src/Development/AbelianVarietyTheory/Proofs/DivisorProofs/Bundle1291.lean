import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivRealOneParamProductLevel
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UAut.JointDer

theorem prod_ofFn_append {G : Type} [Monoid G] {d k : ℕ} (δ : Fin d → ℝ → G) (γ : Fin k → ℝ → G) (s : Fin d → ℝ)
    (t : Fin k → ℝ) :
    (List.ofFn fun i => Fin.append δ γ i (Fin.append s t i)).prod =
      (List.ofFn fun a => δ a (s a)).prod * (List.ofFn fun i => γ i (t i)).prod := by
  have e : (fun i => Fin.append δ γ i (Fin.append s t i)) = Fin.append (fun a => δ a (s a)) (fun i => γ i (t i)) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  rw [e, List.ofFn_fin_append, List.prod_append]

theorem contDiff_append {d k : ℕ} : ContDiff ℝ ∞ fun q : (Fin d → ℝ) × (Fin k → ℝ) => Fin.append q.1 q.2 := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]; exact (contDiff_apply ℝ ℝ a).comp contDiff_fst
  · simp only [Fin.append_right]; exact (contDiff_apply ℝ ℝ j).comp contDiff_snd

theorem iteratedFDeriv_slice {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] {H : A × B → ℂ} (hH : ContDiff ℝ ∞ H) (m : ℕ) (a : A) (t : B) :
    iteratedFDeriv ℝ m (fun t => H (a, t)) t =
      (iteratedFDeriv ℝ m H (a, t)).compContinuousLinearMap fun _ => ContinuousLinearMap.inr ℝ A B := by
  have e : (fun t => H (a, t)) = (fun q => H ((a, 0) + q)) ∘ ContinuousLinearMap.inr ℝ A B := by
    funext t; simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _
    (show ContDiff ℝ ∞ fun q => H ((a, 0) + q) from hH.comp (contDiff_const.add contDiff_id)) _
    (by exact_mod_cast le_top), iteratedFDeriv_comp_add_left]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem commute_prod_realLine {k : ℕ} {γ : Fin k → ℝ → GAd σ J} (hγ : ∀ i, IsRealLine σ J (γ i)) (t : Fin k → ℝ)
    {u : GAd σ J} (hu : u ∈ finPts σ J) : Commute (List.ofFn fun i => γ i (t i)).prod u := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  obtain ⟨w, τ, Z, -, h⟩ := hγ i
  obtain ⟨y, e, -⟩ := h (t i)
  show Commute (γ i (t i)) u
  rw [e]
  exact commute_embArch σ J y (mem_finPts_iff_forall.1 hu w)

end GlobalTheory.UAut.JointDer

open GlobalTheory.UAut.JointDer in

theorem GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) → (∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧ ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u) → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → IsSm σ J φ → ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ m : ℕ, Continuous fun p : GAd σ J × (Fin k → ℝ) => iteratedFDeriv ℝ m (fun t : Fin k → ℝ => φ (p.1 * (List.ofFn fun i => γ i (t i)).prod)) p.2 := by
  intro F E _ _ _ _ _ σ _ n J _ d δ hδ hchart φ hlev hsm k γ hγ m
  obtain ⟨U, hUo, hU⟩ := hlev
  obtain ⟨W, hW, s, hs, hWs⟩ := hchart _ (hUo.mem_nhds U.one_mem)
  set P : (Fin k → ℝ) → GAd σ J := fun t => (List.ofFn fun i => γ i (t i)).prod with hP
  set Q : (Fin d → ℝ) → GAd σ J := fun s => (List.ofFn fun a => δ a (s a)).prod with hQ
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨x₀, t₀⟩ := p₀
  let H : (Fin d → ℝ) × (Fin k → ℝ) → ℂ := fun q => φ (x₀ * (Q q.1 * P q.2))
  have hH : ContDiff ℝ ∞ H := by
    have h1 := hsm (d + k) (Fin.append δ γ)
      (fun i => Fin.addCases (fun a => by simpa [Fin.append_left] using hδ a)
        (fun j => by simpa [Fin.append_right] using hγ j) i) x₀
    have h2 := h1.comp contDiff_append
    convert h2 using 1
    funext q
    simp only [Function.comp_apply, H, prod_ofFn_append, hP, hQ]
  have key : ∀ x, x₀⁻¹ * x ∈ W → ∀ t, φ (x * P t) = H (s (x₀⁻¹ * x), t) := by
    intro x hx t
    obtain ⟨u, huU, huf, e⟩ := hWs _ hx
    have hc : Commute (P t) u := commute_prod_realLine hγ t huf
    have hx' : x = x₀ * (Q (s (x₀⁻¹ * x)) * u) := by
      simp only [hQ]
      rw [← e]
      group
    calc φ (x * P t) = φ (x₀ * (Q (s (x₀⁻¹ * x)) * u) * P t) := by rw [← hx']
      _ = φ ((x₀ * (Q (s (x₀⁻¹ * x)) * P t)) * u) := by
          congr 1
          simp only [mul_assoc]
          rw [hc.eq]
      _ = H (s (x₀⁻¹ * x), t) := hU u huU huf _
  have hev : ∀ᶠ p : GAd σ J × (Fin k → ℝ) in 𝓝 (x₀, t₀),
      (iteratedFDeriv ℝ m H (s (x₀⁻¹ * p.1), p.2)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) =
      iteratedFDeriv ℝ m (fun t => φ (p.1 * P t)) p.2 := by
    have hmem : {p : GAd σ J × (Fin k → ℝ) | x₀⁻¹ * p.1 ∈ W} ∈ 𝓝 (x₀, t₀) :=
      (continuous_const.mul continuous_fst).continuousAt.preimage_mem_nhds (by simpa using hW)
    filter_upwards [hmem] with p hp
    rw [← iteratedFDeriv_slice hH, show (fun t => φ (p.1 * P t)) = fun t => H (s (x₀⁻¹ * p.1), t) from
      funext (key p.1 hp)]
  refine ContinuousAt.congr ?_ hev
  have hcont : Continuous fun q => (iteratedFDeriv ℝ m H q).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) :=
    (ContinuousMultilinearMap.continuous_precomp _).comp (hH.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hsx : ContinuousAt (fun p : GAd σ J × (Fin k → ℝ) => s (x₀⁻¹ * p.1)) (x₀, t₀) :=
    hs.comp_of_eq (continuous_const.mul continuous_fst).continuousAt (by simp)
  exact hcont.continuousAt.comp (hsx.prodMk continuousAt_snd)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMapGLSpl
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

theorem pLoc_idem_spl (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

theorem pLoc_prjG_spl (T : Finset (Pl E)) (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T g) =
      if w ∈ T then GeneralLinearGroup.map (pLoc E w) g else 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pLoc E w (((idem E T • g.val + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))) :
    Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, pLoc_idem_spl]
  split_ifs with h
  · simp
  · simp [Matrix.one_apply, apply_ite (pLoc E w)]

theorem glAf_ext_spl {g h : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun x : GL (Fin n) (w.adicCompletion E) => x.val i j) (H w)

theorem continuous_pLoc_spl (w : Pl E) : Continuous (pLoc E w) :=
  RestrictedProduct.continuous_eval (R := fun w : Pl E => w.adicCompletion E)
    (A := fun w : Pl E => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) w

theorem continuous_sLoc_spl (v : Pl E) : Continuous (sLoc E v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (Pl E)) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun u : Pl E => u.adicCompletion E)
      (fun u => (u.adicCompletionIntegers E : Set (u.adicCompletion E))) (Filter.principal {v}ᶜ) :=
    fun a => ⟨Pi.single v a, fun u hu => by
      rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem continuous_mapGL_spl (w : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_pLoc_spl E w))

theorem continuous_locGL_spl (w : Pl E) : Continuous (locGL E n w) :=
  Continuous.units_map _ (continuous_const.add (Continuous.matrix_map continuous_id (continuous_sLoc_spl E w)))

variable {E n}

def psiG_spl (u : Pl E) (p : GLw n u × GLw n (cPl E u)) : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  locGL E n u p.1 * locGL E n (cPl E u) p.2

theorem pLoc_psiG_self_spl {u : Pl E} (hu : cPl E u ≠ u) (p : GLw n u × GLw n (cPl E u)) :
    GeneralLinearGroup.map (pLoc E u) (psiG_spl u p) = p.1 := by
  rw [psiG_spl, map_mul, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hu), mul_one]

theorem pLoc_psiG_conj_spl {u : Pl E} (hu : cPl E u ≠ u) (p : GLw n u × GLw n (cPl E u)) :
    GeneralLinearGroup.map (pLoc E (cPl E u)) (psiG_spl u p) = p.2 := by
  rw [psiG_spl, map_mul, pLoc_locGL, pLoc_locGL_of_ne hu, one_mul]

theorem pLoc_psiG_of_ne_spl {u w : Pl E} (h1 : w ≠ u) (h2 : w ≠ cPl E u) (p : GLw n u × GLw n (cPl E u)) :
    GeneralLinearGroup.map (pLoc E w) (psiG_spl u p) = 1 := by
  rw [psiG_spl, map_mul, pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]

theorem mem_orb_spl {u w : Pl E} : w ∈ orb E u ↔ w = u ∨ w = cPl E u := by
  simp [orb]

theorem pLoc_gam_of_ne_spl {u w : Pl E} (h1 : w ≠ u) (h2 : w ≠ cPl E u) (g : Gam E n u) :
    GeneralLinearGroup.map (pLoc E w) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) = 1 := by
  obtain ⟨h, hh⟩ := g.2
  rw [← hh, pLoc_prjG_spl, if_neg (by rw [mem_orb_spl]; tauto)]

theorem psiG_mem_spl {u : Pl E} (hu : cPl E u ≠ u) (p : GLw n u × GLw n (cPl E u)) : psiG_spl u p ∈ Gam E n u := by
  refine ⟨psiG_spl u p, glAf_ext_spl E n fun w => ?_⟩
  rw [pLoc_prjG_spl]
  split_ifs with hw
  · rfl
  · rw [mem_orb_spl, not_or] at hw
    rw [pLoc_psiG_of_ne_spl hw.1 hw.2]

theorem rho_apply_spl (u : Pl E) (g : Gam E n u) :
    rho E n u g = (GeneralLinearGroup.map (pLoc E u) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)),
      GeneralLinearGroup.map (pLoc E (cPl E u)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := rfl

def rhoHomeo_spl {u : Pl E} (hu : cPl E u ≠ u) : Gam E n u ≃ₜ GLw n u × GLw n (cPl E u) where
  toFun := rho E n u
  invFun p := ⟨psiG_spl u p, psiG_mem_spl hu p⟩
  left_inv g := by
    refine Subtype.ext (glAf_ext_spl E n fun w => ?_)
    change GeneralLinearGroup.map (pLoc E w) (psiG_spl u (rho E n u g)) = _
    by_cases h1 : w = u
    · subst h1; rw [pLoc_psiG_self_spl hu]; rfl
    by_cases h2 : w = cPl E u
    · subst h2; rw [pLoc_psiG_conj_spl hu]; rfl
    rw [pLoc_psiG_of_ne_spl h1 h2, pLoc_gam_of_ne_spl h1 h2]
  right_inv p := by
    rw [rho_apply_spl]
    exact Prod.ext (pLoc_psiG_self_spl hu p) (pLoc_psiG_conj_spl hu p)
  continuous_toFun :=
    ((continuous_mapGL_spl E n u).comp continuous_subtype_val).prodMk
      ((continuous_mapGL_spl E n (cPl E u)).comp continuous_subtype_val)
  continuous_invFun :=
    Continuous.subtype_mk (((continuous_locGL_spl E n u).comp continuous_fst).mul
      ((continuous_locGL_spl E n (cPl E u)).comp continuous_snd)) _

end GlobalTheory.EulerTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousProduct
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilProduct

open GlobalTheory.FinWeilO GlobalTheory.FinWeil GlobalTheory.SplitScalar

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {χS χT : (AE D)ˣ →* Circle} {of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem actO_mul (g g' : GA D S) (h h' : GA D T) (u : WO S T) :
    actO S T (g * g') (h * h') u = actO S T g h (actO S T g' h' u) := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]

theorem actO_one (u : WO S T) : actO S T 1 1 u = u := by
  unfold actO
  rw [inv_one, mt_one, mt_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_parts (p : GA D S × GA D T) : ∃ a ∈ GinfC S, ∃ b ∈ GinfC T, ∃ k ∈ GfC S, ∃ l ∈ GfC T,
    p = (a, b) * (k, l) ∧ p = (k, l) * (a, b) := by
  obtain ⟨a, ha, k, hk, e1⟩ := (GlobalTheory.UnitarySplit.real_finite_split D S).1 p.1
  obtain ⟨b, hb, l, hl, e2⟩ := (GlobalTheory.UnitarySplit.real_finite_split D T).1 p.2
  refine ⟨a, ha, b, hb, k, hk, l, hl, Prod.ext e1 e2, Prod.ext ?_ ?_⟩
  · exact e1.trans ((GlobalTheory.UnitarySplit.real_finite_split D S).2.1 a ha k hk)
  · exact e2.trans ((GlobalTheory.UnitarySplit.real_finite_split D T).2.1 b hb l hl)

theorem fin_eq_smul (hψ : IsStdChar D ψ (-1)) (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    (hlam : GlobalTheory.FinWeil.GoodNorm (sgO D) lam) {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}
    (h : IsLatRep hψ.1 ΛS ΛT w lam Om) (p : GA D S × GA D T) :
    ∃ c : ℂ, ∀ f : thetaSub ψ S T, of p f = c • (Om p f : WO S T → ℂ) := by
  obtain ⟨a, ha, b, hb, k, hk, l, hl, -, rfl⟩ := exists_parts p
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T) Om
  have ho : ∀ p f (hf : IsThetaFunO ψ S T f), om p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => hom p ⟨f, hf⟩
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ hψ S T (of (k, l) * om (k⁻¹, l⁻¹))
    (fun f h1 => by
      rw [Module.End.mul_apply, ho _ f h1]
      exact hf.pres _ _ (Om _ ⟨f, h1⟩).2)
    (fun u f h1 => by
      obtain ⟨f', e1, e2⟩ := h.Heisenberg₂ hψ (inv_mem hk) (inv_mem hl) u ⟨f, h1⟩
      have e1' : (f' : WO S T → ℂ) = heisO ψ S T u f := e1
      rw [Module.End.mul_apply, Module.End.mul_apply, ← e1', hom, e2, hf.Heisenberg₂ k hk l hl _ _ (Om _ ⟨f, h1⟩).2,
        ← actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one, ho _ f h1])
    (fun μ 𝓕 hμ h𝓕 f h1 => by
      rw [Module.End.mul_apply, ho _ f h1, hf.unit μ 𝓕 hμ h𝓕 _ _ (Om _ ⟨f, h1⟩).2]
      exact h.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, h1⟩)
  refine ⟨c, fun f => ?_⟩
  have e := hc _ (Om (k, l) f).2
  rw [Module.End.mul_apply, hom, ← Module.End.mul_apply, ← map_mul,
    show ((k⁻¹, l⁻¹) : GA D S × GA D T) * (k, l) = 1 from inv_mul_cancel ((k, l) : GA D S × GA D T), map_one,
    Module.End.one_apply] at e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf.triv a ha b hb _ f.2, h.real_triv ha hb, e]

theorem fin_inf_comm (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) (p q : GA D S × GA D T) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  obtain ⟨a, ha, b, hb, k, hk, l, hl, rfl, -⟩ := exists_parts q
  let L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T := (oi (a, b)).restrict fun g hg => hi.pres _ g hg
  have hL : ∀ m, (L m : WO S T → ℂ) = oi (a, b) m := fun _ => rfl
  have e := congrArg Subtype.val (h.comm L (fun x v => Subtype.ext (by
    have e1 := congrArg XF.val (rhoF_real ha hb x)
    rw [coe_rhoF] at e1
    rw [hL, coe_opF, coe_opF, hL, map_smul, hi.Heisenberg₂ a ha b hb _ _ v.2, e1])) p ⟨f, h1⟩)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hi.triv k hk l hl _ h1,
    hi.triv k hk l hl _ (hf.pres _ _ h1), hc ⟨f, h1⟩, map_smul, ← hL, ← e, ← hc]
  rfl

theorem eventually_smul (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {f : WO S T → ℂ} (h1 : IsThetaFunO ψ S T f) :
    ∀ᶠ p in 𝓝 (1 : GA D S × GA D T), ∃ c : ℂ, of p f = c • f := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  filter_upwards [h.eventually_fix hS hT ⟨f, h1⟩] with p hp
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  exact ⟨c, by rw [hc ⟨f, h1⟩, hp]⟩

theorem continuous_product (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) (u : WO S T) : Continuous fun p : GA D S × GA D T => of p (oi p f) u := by
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : IsTopologicalGroup (GA D T) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig T.gram))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (eventually_smul hψ hS hT hf h3)] with p hp
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']

end GlobalTheory.WeilProduct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryLocalComponentToLocalUnitaryGro
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem cLoc_fin_continuous {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) :
    Continuous (fun x : finU E n => cLoc w (x : UA E n)) := by
  have hf : Continuous ((pLoc E w).comp (pFin E)) := by
    show Continuous (fun x => pLoc E w (pFin E x))
    exact (RestrictedProduct.continuous_eval w).comp continuous_snd
  have hm : Continuous (((pLoc E w).comp (pFin E)).mapMatrix : Matrix (Fin n) (Fin n) (Ad E) →+* _) :=
    continuous_id.matrix_map hf
  exact (Continuous.units_map _ hm).comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_toSub {X G : Type} [TopologicalSpace X] [Group G] [TopologicalSpace G] (H : Subgroup G) {f : X → G}
    (hf : Continuous f) (hH : ∀ x, f x ∈ H) : Continuous (fun x => toSub H (f x)) := by
  have : (fun x => toSub H (f x)) = fun x => (⟨f x, hH x⟩ : H) := by
    funext x; simp [toSub, hH x]
  rw [this]
  exact hf.subtype_mk _

theorem toSub_cLoc_continuous_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (hmem : ∀ x : finU E n, cLoc w (x : UA E n) ∈ UL n w) :
    Continuous (fun x : finU E n => toSub (UL n w) (cLoc w (x : UA E n))) :=
  continuous_toSub _ (cLoc_fin_continuous w) hmem

theorem toSub_cLoc_fin_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ w : Pl E, Continuous (fun x : finU E n => toSub (UL n w) (cLoc w (x : UA E n))) := by
  intro E _ _ _ hE n w
  exact toSub_cLoc_continuous_of_mem w (GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hE n w)

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentInverseLimitCompatible
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompatLift

theorem exists_of_compat {O : Type} [CommRing O] (p : O) [IsPrecomplete (Ideal.span {p}) O]
    {W : Type} [AddCommGroup W] [Module O W] [Module.Finite O W]
    {C : ℕ → Type} [∀ n, AddCommGroup (C n)] [∀ n, Module O (C n)]
    (c : ∀ n, W →+ C n) (hsurj : ∀ n, Function.Surjective (c n))
    (hker : ∀ (n : ℕ) (w : W), c n w = 0 → w ∈ (Ideal.span {p ^ n} • ⊤ : Submodule O W))
    (hsmul : ∀ (n : ℕ) (a : O) (w : W), c n (a • w) = a • c n w)
    (hkill : ∀ (n : ℕ) (x : C n), p ^ n • x = 0)
    (u : ∀ n, C n) (hcomp : ∀ (n : ℕ) (w : W), c (n + 1) w = u (n + 1) → c n w = u n) :
    ∃ w : W, ∀ n, c n w = u n := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' O W
  have step : ∀ (n : ℕ) (a : Fin k → O), c n (f a) = u n → ∃ a' : Fin k → O,
      c (n + 1) (f a') = u (n + 1) ∧ ∃ b : Fin k → O, a' = a + p ^ n • b := by
    intro n a ha
    obtain ⟨w', hw'⟩ := hsurj (n + 1) (u (n + 1))
    have h1 : c n (w' - f a) = 0 := by rw [map_sub, hcomp n w' hw', ha, sub_self]
    have h2 := hker n _ h1
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨v, -, hv⟩ := h2
    obtain ⟨b, rfl⟩ := hf v
    refine ⟨a + p ^ n • b, ?_, b, rfl⟩
    rw [map_add, map_smul, hv, add_sub_cancel, hw']
  choose! g hg using step
  let a : ℕ → Fin k → O := fun n => Nat.rec 0 (fun m x => g m x) n
  have h0 : ∀ x : C 0, x = 0 := fun x => by simpa using hkill 0 x
  have ha : ∀ n, c n (f (a n)) = u n := by
    intro n
    induction n with
    | zero => rw [h0 (c 0 _), h0 (u 0)]
    | succ n ih => exact (hg n _ ih).1
  have hd : ∀ n, ∃ b : Fin k → O, a (n + 1) = a n + p ^ n • b := fun n => (hg n _ (ha n)).2
  have hcong : ∀ m n, m ≤ n → ∀ i, ∃ e : O, a n i = a m i + p ^ m * e := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact fun i => ⟨0, by simp⟩
    | succ n hmn ih =>
      intro i
      obtain ⟨e, he⟩ := ih i
      obtain ⟨b, hb⟩ := hd n
      refine ⟨e + p ^ (n - m) * b i, ?_⟩
      rw [hb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, he, ← pow_mul_pow_sub p hmn]
      ring
  have hmem : ∀ (m : ℕ) (x y : O),
      x ≡ y [SMOD (Ideal.span {p} ^ m • ⊤ : Submodule O O)] ↔ ∃ e : O, y = x + p ^ m * e := by
    intro m x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩
      exact ⟨-e, by rw [mul_neg, mul_comm, he]; ring⟩
    · rintro ⟨e, rfl⟩
      exact ⟨-e, by ring⟩
  choose L hL using fun i => IsPrecomplete.prec' (I := Ideal.span {p}) (fun n => a n i)
    fun {m n} hmn => (hmem m _ _).2 (hcong m n hmn i)
  refine ⟨f L, fun n => ?_⟩
  choose e he using fun i => (hmem n _ _).1 (hL i n)
  have hLe : L = a n + p ^ n • e := funext fun i => by
    rw [he i, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hLe, map_add, map_smul, map_add, hsmul, hkill, add_zero, ha]

end GlobalTheory.CompatLift

namespace GlobalTheory.SqZeroPt

theorem cn_hits_compatible : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → (∀ n, Function.Surjective (cn t n)) → (∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A))) → (∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w) → (∀ (n : ℕ) (c : O) (w : Wmod A), cn t n (c • w) = c • cn t n w) → ∀ u : G.omega, ∃ w, ∀ n, cn t n w = u.1 n := by
  intro p O _ _ G A _ t hfin hsurj hker hres hsmul u
  exact GlobalTheory.CompatLift.exists_of_compat (p : O) (C := fun n => GlobalTheory.PDiv.Cot O (G.A n)) (cn t)
    hsurj hker hsmul (fun n x => G.pow_smul_cot n x) (fun n => u.1 n)
    fun n w hw => by rw [← hres n w, hw]; exact u.2 n

end GlobalTheory.SqZeroPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureQuotientSubBlockStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_quotient_sub_block : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η := by
  first | exact @GlobalTheory.blockQS_curv_eq_neg_dbarHol_extFormAdj | exact GlobalTheory.blockQS_curv_eq_neg_dbarHol_extFormAdj | (intros; apply GlobalTheory.blockQS_curv_eq_neg_dbarHol_extFormAdj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarExtensionFormZeroStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_extension_form_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (η₁ η₂ : V), dbarAnti (extForm H) z η₁ η₂ = 0 := by
  first | exact @GlobalTheory.DbarExt.dbarAnti_extForm_eq_zero | exact GlobalTheory.DbarExt.dbarAnti_extForm_eq_zero | (intros; apply GlobalTheory.DbarExt.dbarAnti_extForm_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRangeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU E n) ∧ ∀ x : finU E n, x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  first | exact @GlobalTheory.BCT.FinPart.finPt_props | exact GlobalTheory.BCT.FinPart.finPt_props | (intros; apply GlobalTheory.BCT.FinPart.finPt_props <;> assumption)
end

