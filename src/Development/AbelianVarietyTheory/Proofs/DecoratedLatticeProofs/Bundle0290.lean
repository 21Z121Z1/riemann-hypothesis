import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderedProdLocalPartsSeparatesPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.SepProd

variable {D : D7}

theorem list_ofFn_prod_eq {M : Type*} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ j, j ≠ i → f j = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero j)
    · rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact list_ofFn_prod_eq (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem mem_grpOff_of_suppAt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt p.e V g) {v : GlobalTheory.FinPl.Pl D} (hv : p.v ≠ v) :
    g ∈ grpOff V (· = v) := by
  rw [grpOff, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idOff D (· = v))) (map_zero _) (map_one _), Matrix.map_apply,
    Ideal.Quotient.eq]
  have hmem : Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ idAt D (· = p.v) := by
    have := hg i j
    rw [Matrix.sub_apply] at this
    rw [← this]
    exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.FrameLat.sum_mem_idAt p)
  have h2 := (Ideal.mem_inf.1 hmem).2
  rw [Ideal.mem_iInf] at h2
  rw [idOff, Ideal.mem_iInf]
  rintro ⟨w, rfl⟩
  exact h2 ⟨w, fun e => hv e.symm⟩

end GlobalTheory.SeeSaw.SepProd

open GlobalTheory.SeeSaw.SepProd in

theorem GlobalTheory.SeeSaw.SepProd.prod_sep : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ) (xs : Fin n → GA D (c.V j')), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) → ∀ (i : Fin n), ∃ y ∈ grpOff (c.V j') (· = (G i).q.v), (List.ofFn xs).prod = xs i * y := by
  intro D c v n G hG j' xs hxs i
  refine ⟨(xs i)⁻¹ * (List.ofFn xs).prod, ?_, by rw [mul_inv_cancel_left]⟩
  have hoff : ∀ i', i' ≠ i → xs i' ∈ grpOff (c.V j') (· = (G i).q.v) := fun i' hi' =>
    mem_grpOff_of_suppAt (G i').q (hxs i') fun e => hi' (hG.inj e)
  rw [grpOff, congGrp, MonoidHom.mem_ker, map_mul, map_inv, map_list_prod, List.map_ofFn,
    list_ofFn_prod_eq (_ ∘ xs) i fun j hj => MonoidHom.mem_ker.1 (hoff j hj), Function.comp_apply, inv_mul_cancel]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLinearRelationDensityOfUnfoldingSteps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.DenseRel

variable {D : D7}

theorem sobCont_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Sobolev₂ Lie σ 0 :=
  ⟨[], 0, by simp, by simp⟩

theorem sobCont_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ)
    (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, h1, h2⟩ := h
  refine ⟨S, ‖c‖ * C, h1, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 w hw) (norm_nonneg c)

theorem sobCont_add {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ ℓ' : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ Lie σ ℓ) (h' : Sobolev₂ Lie σ ℓ') : Sobolev₂ Lie σ (ℓ + ℓ') := by
  obtain ⟨S, C, h1, h2⟩ := h
  obtain ⟨S', C', h1', h2'⟩ := h'
  refine ⟨S ++ S', max C C', fun l hl => (List.mem_append.1 hl).elim (h1 l) (h1' l), fun w hw => ?_⟩
  have p : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum := by
    intro S
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  rw [LinearMap.add_apply, List.map_append, List.sum_append, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ((h2 w hw).trans ?_) ((h2' w hw).trans ?_))
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (p S)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (p S')

section Sep

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem sepCont_zero : GlobalTheory.Core.Mi.SepCont M 0 := fun τ _ => ⟨0, sobCont_zero _ _, fun _ => by simp⟩

theorem sepCont_add {Λ Λ' : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) (h' : GlobalTheory.Core.Mi.SepCont M Λ') :
    GlobalTheory.Core.Mi.SepCont M (Λ + Λ') := fun τ v => by
  obtain ⟨ℓ, hℓ, e⟩ := h τ v
  obtain ⟨ℓ', hℓ', e'⟩ := h' τ v
  exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by simp [e, e']⟩

theorem sepCont_smul (a : ℂ) {Λ : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) : GlobalTheory.Core.Mi.SepCont M (a • Λ) :=
  fun τ v => by
    obtain ⟨ℓ, hℓ, e⟩ := h τ v
    exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by simp [e]⟩

theorem sepCont_sum {ι : Type} (s : Finset ι) (Λ : ι → SmT M →ₗ[ℂ] ℂ) (h : ∀ i ∈ s, GlobalTheory.Core.Mi.SepCont M (Λ i)) :
    GlobalTheory.Core.Mi.SepCont M (∑ i ∈ s, Λ i) :=
  Finset.sum_induction Λ (GlobalTheory.Core.Mi.SepCont M) (fun _ _ => sepCont_add M) (sepCont_zero M) h

theorem kill_of_itSpans {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hS : GlobalTheory.Core.Mi.ItSpans M M' It) (Λ : SmT M →ₗ[ℂ] ℂ)
    (h : ∀ P (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y → Λ (It P (PiTensorProduct.tprod ℂ y)) = 0) :
    ∀ v : M.Vec, GlobalTheory.Core.Mi.KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  intro v hv
  have hle : Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧
      x = It P (PiTensorProduct.tprod ℂ y)} ≤ LinearMap.ker Λ := by
    rw [Submodule.span_le]
    rintro x ⟨P, y, hy, rfl⟩
    exact h P y hy
  exact hle (hS v hv)

end Sep

theorem isContAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem isContAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem isContAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact isContAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact isContAut_add hx hy
  | zero => simpa using isContAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact isContAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact isContAut_smul (h x) c

end GlobalTheory.SeeSaw.DenseRel

open GlobalTheory.SeeSaw.DenseRel in

theorem GlobalTheory.SeeSaw.perF_rel_of_steps : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (G : ∀ i, (t (s i)).CC j), (∀ s, (t s).Is) → (∀ i a, IsContAut (c.X j) (φ i a)) → ∀ (W W' : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W' S') (It' : PolF D W'.rank (c.V (j + 1)).rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT (c.M (j + 1))), GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) M' It' → (∀ P₁ P₂ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 (c.It j P₁ (It' P₂ v))) = 0) → ∀ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 v) = 0 := by
  intro hHC D c 𝒯 t hc j ρ h I _ s α φ G ht hφ _W W' S' M' It' hS' hrel
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega

  have hmult : ∀ i, ∃ J χ, (G i).1 ∈ MultT c.θ (c.M j) J χ := fun i => by
    obtain ⟨J, χ, hle⟩ := (ht (s i)).CC j hj
    exact ⟨J, χ, hle (G i).2⟩
  choose J χ hG using hmult
  have hcont : ∀ i x, IsContAut (c.V j) ((G i).1 x) := fun i x => isContAut_multT (hG i) x

  have hL : ∀ (i : I) (a : (t (s i)).Ch j) (g : GA D (c.V j)), ∃ Λ : SmT (c.M j) →ₗ[ℂ] ℂ, GlobalTheory.Core.Mi.SepCont (c.M j) Λ ∧
      ∀ x, Λ x = (c.B j ρ h).per c.ψ (φ i a) (rTrans g ((G i).1 x)) := fun i a g =>
    GlobalTheory.T.besselPeriod_rightTranslate_sobolevSepContinuous D c.θ c.ψ ρ (c.B j ρ h) (c.par j) (c.M j) (J i) (χ i) g (φ i a) hc.inf hc.std (hφ i a) (G i).1 (hG i)
  choose L hLs hLe using hL
  let Λ : SmT (c.M j) →ₗ[ℂ] ℂ :=
    ∑ i, α i • ∑ a, ∑ g ∈ ((t (s i)).e j a).support, ((t (s i)).e j a g) • L i a g
  have hΛ : ∀ x, Λ x = ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 x) := by
    intro x
    simp only [Λ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hLe]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold Tup.perF
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [((GlobalTheory.T.besselPeriod_linear_and_translationCombination D c.ψ hc.std ρ (c.B j ρ h) (φ i a) (hφ i a)).2 _ _ (hcont i x)).2]
  have hΛs : GlobalTheory.Core.Mi.SepCont (c.M j) Λ :=
    sepCont_sum _ _ _ fun i _ => sepCont_smul _ _ (sepCont_sum _ _ _ fun a _ =>
      sepCont_sum _ _ _ fun g _ => sepCont_smul _ _ (hLs i a g))
  have hK : ∀ v : (c.M j).Vec, GlobalTheory.Core.Mi.KVecP (c.M j) v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
    refine kill_of_itSpans (c.M j) (c.M (j + 1)) (c.It j) (hc.span j hj1) Λ fun P y hy => ?_
    exact kill_of_itSpans (c.M (j + 1)) M' It' hS' (Λ ∘ₗ c.It j P)
      (fun P₂ z _ => by simp only [LinearMap.comp_apply, hΛ]; exact hrel P P₂ _) y hy
  have h0 := GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D (c.V j) (c.par j) (c.M j) Λ hΛs hK
  intro v
  rw [← hΛ v, h0, LinearMap.zero_apply]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdLocalParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section

namespace GlobalTheory.LevelCut

open GlobalTheory.SplitCut

variable {D : D7}

theorem entry_idAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2

open GlobalTheory.LocWeil.PlaceIdem in

theorem sum_act {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v)
    (y : AE D) (hy : y ∈ idAt D (fun u => u ∈ Set.range v)) :
    (1 - ∑ w, algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w))) * y = 0 := by
  unfold idAt at hy
  obtain ⟨h1, h2⟩ := hy
  have h1' : infPart D y = 0 := h1
  have h2' : ∀ u, u ∉ Set.range v → compAt D u y = 0 := fun u hu => by
    have := (Ideal.mem_iInf.1 h2) ⟨u, hu⟩
    exact (RingHom.mem_ker).mp this
  have h3 := key v hv y h2'
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)) = 0 := by
    rw [finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  have h4 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 :=
    GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h1', mul_zero, RingHom.map_zero])
      (by rw [RingHom.map_mul, h0, zero_mul, RingHom.map_zero])
  rw [map_sub, map_sub, map_one, map_sum] at h3
  linear_combination h3 + h4

theorem pr_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) :
    q.pr (q.e + cA D q.e) = 1 := by
  have h2 := q.split.2.1
  have ho : q.sec 1 = q.e := by rw [← q.pr.map_one, q.sec_pr, mul_one]
  have p1 : q.pr q.e = 1 := by rw [← ho, q.pr_sec]
  have p2 : q.pr (cA D q.e) = 0 := by rw [← one_mul (q.pr _), ← p1, ← RingHom.map_mul, h2, RingHom.map_zero]
  rw [RingHom.map_add, p1, p2, add_zero]

theorem exists_coord {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y)
    (A B : Matrix (Fin N) (Fin N) k) (h1 : A * B = 1) (h2 : B * A = 1) : ∃ x : GL Y k, A = F.β * x.val * F.γ := by
  have key : ∀ A B : Matrix (Fin N) (Fin N) k, A * B = 1 → (F.γ * A * F.β) * (F.γ * B * F.β) = 1 := fun A B h => by
    calc (F.γ * A * F.β) * (F.γ * B * F.β) = F.γ * (A * (F.β * F.γ) * B) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h, Matrix.mul_one, F.γβ]
  refine ⟨⟨F.γ * A * F.β, F.γ * B * F.β, key A B h1, key B A h2⟩, ?_⟩
  calc A = (F.β * F.γ) * A * (F.β * F.γ) := by rw [F.βγ, Matrix.mul_one, Matrix.one_mul]
    _ = F.β * (F.γ * A * F.β) * F.γ := by simp only [Matrix.mul_assoc]

open GlobalTheory.LocWeil.PlaceIdem in

theorem exists_parts (V : HSp D) {n : ℕ} (v : Fin n → Pl D) (e : Fin n → AE D) (hv : Function.Injective v)
    (he : ∀ w, ∃ ε, IsPlaceIdem D (v w) ε ∧ e w + cA D (e w) = algebraMap (AF D.host.F) (AE D) ε)
    (g : GA D V) (hg : g ∈ grpAt V (fun u => u ∈ Set.range v)) :
    ∃ h : Fin n → GA D V, (∀ w, SuppAt (e w) V (h w)) ∧
      (∀ w, mt V (h w) = (e w + cA D (e w)) • mt V g + (1 - (e w + cA D (e w))) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      g = ((List.finRange n).map h).prod := by
  set E : Fin n → AE D := fun w => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w)) with hEdef
  have hE : ∀ w, e w + cA D (e w) = E w := fun w => by
    obtain ⟨ε, hε, h⟩ := he w
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ w, E w * E w = E w := fun w => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ w, cA D (E w) = E w := fun w => cA_algebraMap _
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hww (hv h)), map_zero]
  choose h hh using fun w => cut_exists V g (E w) (hEE w) (hEc w)
  refine ⟨h, fun w i j => ?_, fun w => ?_, ?_⟩
  · rw [hE w, hh w]
    exact idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j
  · rw [hE w, hh w]
  · apply GlobalTheory.SplitCut.mt_injective
    rw [mt_list_prod V h E _ hh hEo _ (List.nodup_finRange n), ← Fin.sum_univ_def]
    exact exists_widePullback_of_iteratedLine _ _ fun i j => sum_act v hv _ (entry_idAt V _ g hg i j)

theorem prod_local_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G →
    ∀ (j : ℕ) (k : GA D (c.V j)), k ∈ grpAt (c.V j) (· ∈ v.gP) → ∃ h : Fin n → GA D (c.V j),
      (∀ i b hb, ∃ x, (G i).Mat j b hb k x ∧ (ofSplit (G i).q).IsLoc ((G i).FY j b hb) (h i) x) ∧
        k = ((List.finRange n).map h).prod := by
  intro D c v n G hG j g hg
  have hP : (fun u => u ∈ v.gP) = fun u => u ∈ Set.range (fun i => (G i).q.v) := by
    funext u
    rw [hG.places u]
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  rw [hP] at hg
  obtain ⟨h, h1, h2, h3⟩ := exists_parts (c.V j) (fun i => (G i).q.v) (fun i => (G i).q.e) hG.inj
    (fun i => (G i).q.above) g hg
  refine ⟨h, fun i b hb => ?_, h3⟩
  have hm : ∀ a a' : GA D (c.V j), a * a' = 1 →
      (mt (c.V j) a).map (G i).q.pr * (mt (c.V j) a').map (G i).q.pr = 1 := fun a a' ha => by
    rw [← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, ha, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  obtain ⟨x, hx⟩ := exists_coord ((G i).FY j b hb) _ _ (hm g g⁻¹ (mul_inv_cancel g)) (hm g⁻¹ g (inv_mul_cancel g))
  refine ⟨x, hx, h1 i, ?_⟩
  change (mt (c.V j) (h i)).map (G i).q.pr = _
  rw [h2 i, GlobalTheory.GfCut.map_idem, pr_sum, one_smul, sub_self, zero_smul, add_zero]
  exact hx

end GlobalTheory.LevelCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfIteratedFiniteIntegrals
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VanCore

theorem quotient_integral_weighted_sum {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → G → ℂ) (z : ι → ℂ) (h : ∀ i ∈ s, IsQuotIntL1 μR μG (f i) (z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i ∈ s, c i * f i x) (∑ i ∈ s, c i * z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert (IsQuotIntL1.zero : IsQuotIntL1 μR μG 0 0) using 1
    · funext x; simp
    · simp
  | insert i s hi ih =>
    have h1 := (h i (Finset.mem_insert_self i s)).smul (c i)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    convert h1.add h2 using 1
    · funext x; simp [Finset.sum_insert hi]
    · simp [Finset.sum_insert hi]

theorem vanish : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁] [LocallyCompactSpace G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [LocallyCompactSpace G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (A₁ B₁ R₁ : Subgroup G₁) (A₂ B₂ R₂ : Subgroup G₂), IsClosed (A₁ : Set G₁) → IsClosed (B₁ : Set G₁) → IsClosed (R₁ : Set G₁) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a) → (∃ e : (A₁ × B₁) ≃ₜ G₁, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b ∈ R₁ → a ∈ R₁ ∧ b ∈ R₁) → IsClosed (A₂ : Set G₂) → IsClosed (B₂ : Set G₂) → IsClosed (R₂ : Set G₂) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b = b * a) → (∃ e : (A₂ × B₂) ≃ₜ G₂, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b ∈ R₂ → a ∈ R₂ ∧ b ∈ R₂) → ∀ (μR₁ : Measure R₁) (μG₁ : Measure G₁) (ρ₁ : Measure (R₁.subgroupOf B₁)) (μ₁ : Measure B₁) (μR₂ : Measure R₂) (μG₂ : Measure G₂) (ρ₂ : Measure (R₂.subgroupOf B₂)) (μ₂ : Measure B₂), μR₁.IsHaarMeasure → μR₁.IsInvInvariant → μG₁.IsHaarMeasure → ρ₁.IsHaarMeasure → ρ₁.IsInvInvariant → μ₁.IsHaarMeasure → μ₁.IsMulRightInvariant → μR₂.IsHaarMeasure → μR₂.IsInvInvariant → μG₂.IsHaarMeasure → ρ₂.IsHaarMeasure → ρ₂.IsInvInvariant → μ₂.IsHaarMeasure → ∀ (K : Subgroup G₁) (C : Set G₁) (T : Finset G₁), K ≤ B₁ → IsCompact (K : Set G₁) → IsOpen ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁) → IsCompact C → C ⊆ (B₁ : Set G₁) → (∀ q ∈ T, q ∈ B₁) → ∀ (F₁ : G₁ → ℂ) (F₂ : G₁ → G₂ → ℂ) (z : ℂ), IsQuotIntL1 μR₁ μG₁ F₁ z → (∀ h₁, IsQuotIntL1 μR₂ μG₂ (F₂ h₁) (F₁ h₁)) → (∀ h₁, ∀ k ∈ K, F₂ (h₁ * k) = F₂ h₁) → (∀ h₁, F₂ h₁ ≠ 0 → ∃ q ∈ T, ∃ r ∈ R₁, ∃ a ∈ A₁, ∃ k ∈ C, h₁ = r * a * q * k) → (∀ a ∈ A₁, ∀ a' ∈ A₂, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun (q₁ : B₁) (q₂ : B₂) => F₂ (a * q₁.1) (a' * q₂.1)) 0) → z = 0 := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A₁ B₁ R₁ A₂ B₂ R₂ hA₁ hB₁ hR₁ hc₁ he₁ hs₁ hA₂ hB₂ hR₂ hc₂ he₂ hs₂
    μR₁ μG₁ ρ₁ μ₁ μR₂ μG₂ ρ₂ μ₂ i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 K C T hKB hKc hKo hCc hCB hTB
    F₁ F₂ z hF₁ hF₂ hFK hsupp hIter
  classical
  haveI : LocallyCompactSpace B₁ := hB₁.locallyCompactSpace
  haveI : LocallyCompactSpace B₂ := hB₂.locallyCompactSpace
  have hR₁B : IsClosed ((R₁.subgroupOf B₁ : Subgroup B₁) : Set B₁) := by
    rw [Subgroup.coe_subgroupOf]; exact hR₁.preimage continuous_subtype_val
  have hR₂B : IsClosed ((R₂.subgroupOf B₂ : Subgroup B₂) : Set B₂) := by
    rw [Subgroup.coe_subgroupOf]; exact hR₂.preimage continuous_subtype_val

  have FK : ∀ h, ∀ k ∈ K, F₁ (h * k) = F₁ h := fun h k hk => by
    have h1 := hF₂ (h * k)
    rw [hFK h k hk] at h1
    exact (IsQuotIntL1.unique hR₂ (hF₂ h) h1).symm
  have FZ : ∀ h, F₂ h = 0 → F₁ h = 0 := fun h h0 => by
    have h1 := hF₂ h
    rw [h0] at h1
    exact (GlobalTheory.QuotZero.left_and_zero hR₂ μR₂ μG₂ h1).2 rfl
  have FL := (GlobalTheory.QuotZero.left_and_zero hR₁ μR₁ μG₁ hF₁).1

  have hCb : IsCompact (Subtype.val ⁻¹' C : Set B₁) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]
    · exact hCc
    · intro x hx; exact ⟨⟨x, hCB hx⟩, rfl⟩
  have hKbc : IsCompact ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁) := by
    rw [Subgroup.coe_subgroupOf, Subgroup.coe_subtype, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]
    · exact hKc
    · intro x hx; exact ⟨⟨x, hKB hx⟩, rfl⟩
  have hKint : (interior ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁)).Nonempty := by
    rw [hKo.interior_eq]; exact ⟨1, (K.subgroupOf B₁).one_mem⟩
  obtain ⟨S, hS⟩ := compact_covered_by_mul_left_translates hCb hKint
  let T'' : Finset B₁ := ((T.subtype (· ∈ B₁)) ×ˢ S).image (fun p => p.1 * p.2⁻¹)

  have cell : ∀ a ∈ A₁, ∀ q : B₁, F₂ (a * q) ≠ 0 →
      ∃ q' ∈ T'', ∃ r ∈ R₁.subgroupOf B₁, ∃ k ∈ K.subgroupOf B₁, q = r * q' * k := by
    intro a ha q hq
    obtain ⟨q₀, hq₀, r, hr, a'', ha'', k, hk, hdec⟩ := hsupp _ hq
    obtain ⟨e, he⟩ := he₁
    obtain ⟨⟨pa, pb⟩, hp⟩ : ∃ p, e.symm r = p := ⟨_, rfl⟩
    have hrp : r = (pa : G₁) * pb := by rw [← he (pa, pb), ← hp, e.apply_symm_apply]
    subst hrp
    have hpR := hs₁ _ pa.2 _ pb.2 hr
    have hkB : k ∈ B₁ := hCB hk
    have hq₀B : q₀ ∈ B₁ := hTB q₀ hq₀
    have key : e (⟨a, ha⟩, q) = e (pa * ⟨a'', ha''⟩, pb * ⟨q₀, hq₀B⟩ * ⟨k, hkB⟩) := by
      rw [he, he]
      show a * (q : G₁) = ((pa : G₁) * a'') * ((pb : G₁) * q₀ * k)
      rw [hdec, mul_assoc (pa : G₁) pb a'', ← hc₁ a'' ha'' pb pb.2]
      simp only [mul_assoc]
    have hq' : q = pb * ⟨q₀, hq₀B⟩ * ⟨k, hkB⟩ := congrArg Prod.snd (e.injective key)
    obtain ⟨g, hgS, hg⟩ := Set.mem_iUnion₂.1 (hS (show (⟨k, hkB⟩ : B₁) ∈ (Subtype.val ⁻¹' C : Set B₁) from hk))
    refine ⟨⟨q₀, hq₀B⟩ * g⁻¹, ?_, pb, ?_, g * ⟨k, hkB⟩, hg, ?_⟩
    · exact Finset.mem_image.2 ⟨(⟨q₀, hq₀B⟩, g), Finset.mem_product.2 ⟨Finset.mem_subtype.2 hq₀, hgS⟩, rfl⟩
    · exact Subgroup.mem_subgroupOf.2 hpR.2
    · rw [hq']; group
  obtain ⟨T', w, -, hW⟩ := GlobalTheory.CellInt.quotInt_finiteCells B₁ (R₁.subgroupOf B₁) (K.subgroupOf B₁) hR₁B hKbc hKo
    ρ₁ μ₁ inferInstance inferInstance inferInstance inferInstance T''
  refine GlobalTheory.T.quotientIntegral_vanish_of_commutingProduct G₁ A₁ B₁ R₁ hA₁ hB₁ hR₁ hc₁ he₁ hs₁ μR₁ μG₁ ρ₁ μ₁ inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance F₁ z hF₁ ?_
  intro a ha
  have h1 := hW (fun b => F₁ (a * b.1))
    (fun r hr g => by
      show F₁ (a * ((r : G₁) * g)) = F₁ (a * g)
      rw [← mul_assoc, hc₁ a ha r r.2, mul_assoc]
      exact FL _ (Subgroup.mem_subgroupOf.1 hr) _)
    (fun k hk g => by
      show F₁ (a * ((g : G₁) * k)) = F₁ (a * g)
      rw [← mul_assoc]
      exact FK _ _ (Subgroup.mem_subgroupOf.1 hk))
    (fun g hg => cell a ha g (fun h0 => hg (FZ _ h0)))
  suffices hsum : ∑ q ∈ T', w q * F₁ (a * q.1) = 0 by
    convert h1 using 1; exact hsum.symm
  refine GlobalTheory.T.quotientIntegral_vanish_of_commutingProduct G₂ A₂ B₂ R₂ hA₂ hB₂ hR₂ hc₂ he₂ hs₂ μR₂ μG₂ ρ₂ μ₂ inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (fun h₂ => ∑ q ∈ T', w q * F₂ (a * q.1) h₂) _
    (quotient_integral_weighted_sum T' w (fun q => F₂ (a * q.1)) (fun q => F₁ (a * q.1)) (fun q _ => hF₂ _)) ?_
  intro a' ha'
  obtain ⟨f₁, hf₁0, hf₁q⟩ := hIter a ha a' ha'
  have hs := quotient_integral_weighted_sum T' w (fun q (b : B₂) => F₂ (a * q.1) (a' * b.1)) f₁ (fun q _ => hf₁q q)
  have hf₁ : IsQuotIntL1 ρ₁ μ₁ f₁ (∑ q ∈ T', w q * f₁ q) := hW f₁
    (GlobalTheory.QuotZero.left_and_zero hR₁B ρ₁ μ₁ hf₁0).1
    (fun k hk g => by
      have h2 : IsQuotIntL1 ρ₂ μ₂ (fun q₂ : B₂ => F₂ (a * g.1) (a' * q₂.1)) (f₁ (g * k)) := by
        have h3 := hf₁q (g * k)
        have e3 : (fun q₂ : B₂ => F₂ (a * (g * k).1) (a' * q₂.1)) = fun q₂ : B₂ => F₂ (a * g.1) (a' * q₂.1) := by
          funext q₂
          rw [Subgroup.coe_mul, ← mul_assoc, hFK _ _ (Subgroup.mem_subgroupOf.1 hk)]
        exact e3 ▸ h3
      exact IsQuotIntL1.unique hR₂B h2 (hf₁q g))
    (fun g hg => cell a ha g (fun h0 => hg ((GlobalTheory.QuotZero.left_and_zero hR₂B ρ₂ μ₂ (hf₁q g)).2
      (by funext q₂; simp [h0]))))
  have hz := IsQuotIntL1.unique hR₁B hf₁ hf₁0
  rw [hz] at hs
  exact hs

end GlobalTheory.VanCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DStepCell

variable {D : D7}

def integ {c : Comm D} (v : VCom c) {t : Tup c} (w : VTup t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ)
    (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ)
    (q₁ : GA D (c.V (j + 1))) (q₂ : GA D (c.V (j + 1 + 1))) : ℂ :=
  ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
    (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h)
      (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))
      (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁ q₂) (rTrans q₂ f)

end GlobalTheory.DStepCell

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIntegrandContinuousPeriodicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_contraction_integrand_continuous_periodic : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → Continuous (fun p : Mx D B'.L.rank S.rank × (WO B.A S × WO S B'.A) => f₂ ((B'.o.resT S).symm (p.2.2, p.1)) * f₁ ((B.o.resS S).symm (p.2.1, l.κ S p.1))) ∧ ∀ γ ∈ ratMx D B'.L.rank S.rank, ∀ (w : Mx D B'.L.rank S.rank) (u : WO B.A S) (v : WO S B'.A), f₂ ((B'.o.resT S).symm (v, γ + w)) * f₁ ((B.o.resS S).symm (u, l.κ S (γ + w))) = f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w)) := by
  first | exact @GlobalTheory.ContrComb.integrand_cont_per | exact GlobalTheory.ContrComb.integrand_cont_per | (intros; apply GlobalTheory.ContrComb.integrand_cont_per <;> assumption)
end

