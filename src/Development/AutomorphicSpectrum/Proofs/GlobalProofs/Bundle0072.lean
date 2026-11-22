import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0070
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0050
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryAdelicUnipotentLift
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_part_le_levi : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)), uPart D.sp.cm.sig V.gram X Y T ≤ levi D.sp.cm.sig V.gram X Y T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceUnitaryEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.WittCompl

theorem hT_coords {D : D7} (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) =
      ∑ k, ∑ l, star (a k) * V.gram k l * b l := by
  simp only [Module.Basis.equivFun_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, HSpace.gram,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hT_cols {D : D7} (V : HSp D) {m : ℕ} (A B : Matrix (Fin V.rank) (Fin m) D.host.E) (i j : Fin m) :
    V.hT (V.frame.equivFun.symm fun k => A k i) (V.frame.equivFun.symm fun k => B k j) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) i j := by
  rw [hT_coords]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_perp {E : Type} [Field E] [NumberField E] [StarRing E] (hst : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (V : HSpace E) {n : ℕ} (c d : Fin n → V.V) (hcc : ∀ i j, V.hT (c i) (c j) = 0)
    (hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0) :
    ∃ (V' : HSpace E) (ι : V'.V →ₗ[E] V.V), HSpace.IsIsomEmb V' V ι ∧
      ∀ v, v ∈ LinearMap.range ι ↔ ∀ i, V.hT (c i) v = 0 ∧ V.hT (d i) v = 0 := by
  classical
  have hs := V.herm
  have hdc : ∀ i j, V.hT (d i) (c j) = if i = j then 1 else 0 := fun i j => by
    rw [← hs.eq (c j) (d i), hcd]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : LinearIndependent E c := Fintype.linearIndependent_iff.2 fun g hg j => by
    have := congrArg (V.hT (d j)) hg
    simpa [map_sum, hdc] using this
  obtain ⟨V', ι, hr, hι, h0⟩ := GlobalTheory.WittLow.exists_lower hst V c hc hcc
  have h0' : ∀ x a, V.hT (c a) (ι x) = 0 := fun x a => by rw [← hs.eq (ι x) (c a), h0, map_zero]
  let p : V.V →ₗ[E] V.V := LinearMap.id - ∑ k, (V.hT (d k)).smulRight (c k)
  have hp : ∀ v, p v = v - ∑ k, V.hT (d k) v • c k := fun v => by simp [p, LinearMap.sum_apply]
  have hcp : ∀ a v, V.hT (c a) (p v) = V.hT (c a) v := fun a v => by simp [hp, map_sum, hcc]
  have hdp : ∀ a v, V.hT (d a) (p v) = 0 := fun a v => by simp [hp, map_sum, hdc]
  have hiso : HSpace.IsIsomEmb V' V (p ∘ₗ ι) := fun x y => by
    rw [← hι x y]
    show V.hT (p (ι x)) (p (ι y)) = V.hT (ι x) (ι y)
    have e1 : V.hT (ι x) (p (ι y)) = V.hT (ι x) (ι y) := by simp [hp, map_sum, h0]
    rw [hp (ι x), map_sub, LinearMap.sub_apply, e1, map_sum, LinearMap.sum_apply]
    simp [hcp, h0']
  have hinj : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun x hx =>
    V'.nondeg.1 x fun y => by rw [← hι x y, hx]; simp
  set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (c j)) with hP
  have hdisj : Disjoint (LinearMap.range ι) (Submodule.span E (Set.range c)) := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have : x = 0 := V'.nondeg.1 x fun y => by
      rw [← hι x y, ← hg]
      simp [map_sum, LinearMap.sum_apply, h0']
    rw [this, map_zero]
  have hle : LinearMap.range ι ⊔ Submodule.span E (Set.range c) ≤ P :=
    sup_le (by rintro _ ⟨x, rfl⟩; exact funext fun j => h0' x j)
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact funext fun a => hcc a j))
  have heq : LinearMap.range ι ⊔ Submodule.span E (Set.range c) = P := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ι) (Submodule.span E (Set.range c))
    rw [hdisj.eq_bot, finrank_bot, LinearMap.finrank_range_of_inj hinj, finrank_span_eq_card hc, Fintype.card_fin] at e1
    have e2 := GlobalTheory.WittLow.finrank_orth hs V.nondeg c hc
    have e3 : Module.finrank E V'.V = V'.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V'.frame
    have e4 : Module.finrank E V.V = V.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V.frame
    rw [← hP] at e2
    omega
  refine ⟨V', p ∘ₗ ι, hiso, fun v => ⟨?_, fun hv => ?_⟩⟩
  · rintro ⟨x, rfl⟩ i
    exact ⟨(hcp i _).trans (h0' x i), hdp i _⟩
  · have hvP : v ∈ P := funext fun j => (hv j).1
    rw [← heq] at hvP
    obtain ⟨_, ⟨x, rfl⟩, u, hu, rfl⟩ := Submodule.mem_sup.1 hvP
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hu
    refine ⟨x, ?_⟩
    have hg : ∀ k, V.hT (d k) (ι x) = -g k := fun k => by
      have := (hv k).2
      simp [map_sum, hdc] at this
      exact eq_neg_of_add_eq_zero_left this
    show p (ι x) = _
    simp [hp, hg, sub_eq_add_neg]

theorem exists_compl : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι ∧ ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 := by
  intro D V m X Y h T
  classical
  let e := Fintype.equivFin {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}
  let c : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => X j (e.symm k).1
  let d : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => Y j (e.symm k).1
  have hcc : ∀ i j, V.hT (c i) (c j) = 0 := fun i j => by
    simp only [c]
    rw [hT_cols, h.xx]
    rfl
  have hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0 := fun i j => by
    simp only [c, d]
    rw [hT_cols, h.xy, Matrix.one_apply]
    simp only [Subtype.val_inj, e.symm.apply_eq_iff_eq]
  obtain ⟨V', ι, hι, hr⟩ := exists_perp Formalism.BasicNotions.Examples₂.star_isIntegral V c d hcc hcd
  refine ⟨V', ι, hι, fun v => ?_⟩
  rw [hr]
  constructor
  · intro hv i hi
    have := hv (e ⟨i, hi⟩)
    simpa [c, d] using this
  · intro hv k
    exact hv _ (e.symm k).2

end GlobalTheory.CompanionTheory.WittCompl

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.StandardThreeBlockIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.ZFin

open Polynomial in

theorem commute_aeval {M : Type} [AddCommGroup M] [Module ℂ M] {T S : Module.End ℂ M} (h : Commute S T) (q : ℂ[X]) :
    Commute S (aeval T q) := by
  rw [Polynomial.aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _

open Polynomial in

theorem aeval_modByMonic {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {p : ℂ[X]} {w : M}
    (hw : aeval T p w = 0) (q : ℂ[X]) : aeval T q w = aeval T (q %ₘ p) w := by
  conv_lhs => rw [← Polynomial.modByMonic_add_div q p]
  rw [map_add, LinearMap.add_apply, mul_comm, map_mul, Module.End.mul_apply, hw, map_zero, add_zero]

open Polynomial in

theorem exists_step {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {p : ℂ[X]} (hp : p.Monic)
    {W : Submodule ℂ M} (hF : W.FG) (hW : ∀ w ∈ W, aeval T p w = 0) :
    ∃ W' : Submodule ℂ M, W'.FG ∧ W ≤ W' ∧ (∀ w ∈ W', T w ∈ W') ∧
      (∀ S : Module.End ℂ M, Commute S T → (∀ w ∈ W, S w ∈ W) → ∀ w ∈ W', S w ∈ W') ∧
      (∀ S : Module.End ℂ M, Commute S T → (∀ w ∈ W, S w = 0) → ∀ w ∈ W', S w = 0) := by
  let B : ℂ[X] →ₗ[ℂ] M →ₗ[ℂ] M := (aeval T).toLinearMap
  have hB : ∀ q w, B q w = aeval T q w := fun _ _ => rfl
  have hdeg : ∀ q : ℂ[X], q %ₘ p ∈ degreeLT ℂ p.natDegree := fun q => by
    rw [Polynomial.mem_degreeLT, ← Polynomial.degree_eq_natDegree hp.ne_zero]
    exact Polynomial.degree_modByMonic_lt q hp
  have hmem : ∀ q, ∀ w ∈ W, aeval T q w ∈ Submodule.map₂ B (degreeLT ℂ p.natDegree) W := fun q w hw => by
    rw [aeval_modByMonic T (hW w hw) q]
    exact Submodule.apply_mem_map₂ B (hdeg q) hw
  have hfg : (degreeLT ℂ p.natDegree).FG := by
    rw [← Module.Finite.iff_fg]
    exact Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ p.natDegree).symm
  refine ⟨Submodule.map₂ B (degreeLT ℂ p.natDegree) W, Submodule.FG.map₂ _ hfg hF, fun w hw => ?_, ?_, ?_, ?_⟩
  · simpa using hmem 1 w hw
  · have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤
        (Submodule.map₂ B (degreeLT ℂ p.natDegree) W).comap T :=
      Submodule.map₂_le.2 fun q _ w hw => by
        have e : T * aeval T q = aeval T (X * q) := by rw [map_mul, Polynomial.aeval_X]
        rw [Submodule.mem_comap, hB, ← Module.End.mul_apply, e]
        exact hmem _ w hw
    exact fun w hw => this hw
  · intro S hS hSW
    have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤
        (Submodule.map₂ B (degreeLT ℂ p.natDegree) W).comap S :=
      Submodule.map₂_le.2 fun q _ w hw => by
        rw [Submodule.mem_comap, hB, ← Module.End.mul_apply, (commute_aeval hS q).eq, Module.End.mul_apply]
        exact hmem _ _ (hSW w hw)
    exact fun w hw => this hw
  · intro S hS hSW
    have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤ LinearMap.ker S :=
      Submodule.map₂_le.2 fun q _ w hw => by
        rw [LinearMap.mem_ker, hB, ← Module.End.mul_apply, (commute_aeval hS q).eq, Module.End.mul_apply,
          hSW w hw, map_zero]
    exact fun w hw => this hw

open Polynomial in

theorem exists_fg_stable {M ι : Type} [AddCommGroup M] [Module ℂ M] [Fintype ι] (T : ι → Module.End ℂ M)
    (p : ι → ℂ[X]) (hp : ∀ i, (p i).Monic) (hc : ∀ i j, Commute (T i) (T j)) (v : M)
    (hv : ∀ i, aeval (T i) (p i) v = 0) :
    ∃ W : Submodule ℂ M, W.FG ∧ v ∈ W ∧ ∀ i, ∀ w ∈ W, T i w ∈ W := by
  classical
  have key : ∀ s : Finset ι, ∃ W : Submodule ℂ M, W.FG ∧ v ∈ W ∧ (∀ i ∈ s, ∀ w ∈ W, T i w ∈ W) ∧
      ∀ i, ∀ w ∈ W, aeval (T i) (p i) w = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Submodule.span ℂ {v}, Submodule.fg_span_singleton v, Submodule.mem_span_singleton_self v,
        by simp, fun i w hw => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul, hv, smul_zero]
    | insert j s _ ih =>
      obtain ⟨W, hF, hvW, hs, hk⟩ := ih
      obtain ⟨W', hF', hle, hT, hS, hZ⟩ := exists_step (T j) (hp j) hF (hk j)
      refine ⟨W', hF', hle hvW, fun i hi => ?_, fun i => ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hT
        · exact hS _ (hc i j) (hs i hi)
      · exact hZ _ ((commute_aeval (hc j i) (p i)).symm) (hk i)
  obtain ⟨W, hF, hvW, hs, _⟩ := key Finset.univ
  exact ⟨W, hF, hvW, fun i => hs i (Finset.mem_univ i)⟩

section Main

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.SmoothForms

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

abbrev unitOp (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : Fin V.rank → Fin V.rank → Module.End ℂ (SmFun θ V) :=
  fun a b => derEnd hθ τ (Matrix.single a b 1)

theorem commute_derEnd_gelfA (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : ℕ) :
    Commute (derEnd hθ τ Z) (gelfA (unitOp hθ V τ') k) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have e1 : ∀ g : SmFun θ V, (gelfA (unitOp hθ V τ') k g).1 = gelf θ V τ' k g.1 := fun g => (gelf_eq hθ τ' k g).symm
  have L := linOnSm_gelf (θ := θ) (V := V) τ' k
  refine LinearMap.ext fun f => Subtype.ext ?_
  change RderC θ V τ Z (gelfA (unitOp hθ V τ') k f).1 = (gelfA (unitOp hθ V τ') k (derEnd hθ τ Z f)).1
  rw [e1, e1]
  change _ = gelf θ V τ' k (RderC θ V τ Z f.1)
  simp only [RderC]
  rw [L.add _ (Rder_mem f.2 h1) _ (Submodule.smul_mem _ _ (Rder_mem f.2 h2)), L.smul,
    GlobalTheory.CuspLie.gelf_Rder hθ h1 f.2, GlobalTheory.CuspLie.gelf_Rder hθ h2 f.2]

theorem commute_gelfA (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (k k' : ℕ) :
    Commute (gelfA (unitOp hθ V τ) k) (gelfA (unitOp hθ V τ') k') := by
  refine Commute.sum_left _ _ _ fun idx _ => Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
  exact commute_derEnd_gelfA hθ τ τ' _ k'

open Polynomial in

theorem foldr_gelf_eq (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) (φ : SmFun θ V) (L : List ℂ) :
    L.foldr (fun a f => gelf θ V τ k f - a • f) φ.1 =
      (aeval (gelfA (unitOp hθ V τ) k) ((L.map fun a => (X - C a : ℂ[X])).prod) φ).1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih, gelf_eq hθ τ k, map_mul, map_sub, aeval_X, aeval_C, Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
    rfl

open Polynomial in
theorem monic_prod_roots (L : List ℂ) : ((L.map fun a => (X - C a : ℂ[X])).prod).Monic := by
  induction L with
  | nil => simp
  | cons a L ih => simpa using (monic_X_sub_C a).mul ih

end Main

end GlobalTheory.CompanionTheory.ZFin

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.SmoothForms GlobalTheory.CompanionTheory.ZFin in
open Polynomial in

theorem GlobalTheory.CompanionTheory.ZFin.isAutFunSm_of_gelf_roots : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) → (∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) → (∀ τ k, ∃ L : List ℂ, L.foldr (fun a f => gelf θ V τ k f - a • f) φ = 0) → IsAutFunSm θ V φ := by
  intro D θ hθ V φ hA hs hg hz
  choose L hL using hz
  have hsm : φ ∈ SmFun θ V := hs
  obtain ⟨W, hF, hv, hS⟩ := exists_fg_stable (ι := D.what₂.Tau × Fin V.rank)
    (fun i => gelfA (unitOp hθ V i.1) i.2.val)
    (fun i => ((L i.1 i.2.val).map fun a => (X - C a : ℂ[X])).prod)
    (fun i => monic_prod_roots _) (fun i j => commute_gelfA hθ _ _ _ _) ⟨φ, hsm⟩
    (fun i => Subtype.ext ((foldr_gelf_eq hθ i.1 i.2.val ⟨φ, hsm⟩ _).symm.trans (hL _ _)))
  refine { toIsAutFun := hA, smooth := hs, growth := hg,
           zfin := ⟨W.map (SmFun θ V).subtype, Module.Finite.iff_fg.2 (hF.map _), ⟨⟨φ, hsm⟩, hv, rfl⟩, ?_⟩ }
  rintro τ k _ ⟨f, hf, rfl⟩
  have hstab : ∀ x ∈ Algebra.adjoin ℂ (Set.range fun k : Fin V.rank => gelfA (unitOp hθ V τ) k.val),
      ∀ w ∈ W, x w ∈ W := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hS (τ, j)
    | algebraMap r =>
      intro w hw
      simpa using W.smul_mem r hw
    | add x y _ _ hx hy => exact fun w hw => add_mem (hx w hw) (hy w hw)
    | mul x y _ _ hx hy => exact fun w hw => hx _ (hy w hw)
  exact ⟨_, hstab _ (gelfA_mem_adjoin_low _ _ _ (GlobalTheory.Mem.Lift.glRel_derEnd hθ V τ) k) f hf, (gelf_eq hθ τ k f).symm⟩

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryAdelicUnipotentLiftStatement
section
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_embedding_parabolic_compatibility : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (k : Fin r), k ∈ T → ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J),
      GlobalTheory.BlockForms.IsBlockEmb σ J X Y h ι → k.val + 1 = l + d → 1 ≤ d →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ T) → (l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) →
      glPart σ J X Y T k = ι.range := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange.glPart_eq_range | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange.glPart_eq_range | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange.glPart_eq_range <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryElementPrescribedBlocks
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

def compHom {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau) :
    AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ := (θ τ).comp (infPart D)

theorem adele_ext {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    {a b : AF D.host.F ⊗[D.host.F] D.host.E} (hf : finPart D a = finPart D b)
    (hc : ∀ τ, compHom θ τ a = compHom θ τ b) : a = b := by
  obtain ⟨w, -, hw⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ 1 1 hθ (fun _ _ _ => 0)
  have h0 : ∀ c : AF D.host.F ⊗[D.host.F] D.host.E, finPart D c = 0 → (∀ τ, compHom θ τ c = 0) → c = 0 := by
    intro c h1 h2
    have e1 : (Matrix.of fun _ _ => c : Matrix (Fin 1) (Fin 1) _) = w := hw _ ⟨by
      ext i j
      exact h1, fun τ => by
      ext i j
      exact h2 τ⟩
    have e2 : (0 : Matrix (Fin 1) (Fin 1) (AF D.host.F ⊗[D.host.F] D.host.E)) = w := hw _ ⟨by
      ext i j
      exact map_zero (finPart D), fun τ => by
      ext i j
      exact map_zero (compHom θ τ)⟩
    exact congrFun (congrFun (e1.trans e2.symm) 0) 0
  refine sub_eq_zero.1 (h0 _ ?_ fun τ => ?_)
  · rw [map_sub, hf, sub_self]
  · rw [map_sub, hc, sub_self]

theorem compHom_adMat {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (Y : Matrix (Fin a) (Fin b) D.host.E) :
    (adMat D.host.F Y).map (compHom θ τ) = Y.map (tauE D τ) := by
  ext i j
  have : infPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] Y i j := by
    simp [infPart]
  simp only [Matrix.map_apply, adMat, compHom, RingHom.comp_apply]
  show θ τ (infPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j)) = _
  rw [this]
  exact (hθ τ).1 _

theorem map_one_add_of {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n a b : ℕ}
    (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin a) (Fin n) A) (R : Matrix (Fin n) (Fin b) A) (S : Matrix (Fin b) (Fin n) A)
    {p : Matrix (Fin n) (Fin a) B} {q : Matrix (Fin a) (Fin n) B} {r : Matrix (Fin n) (Fin b) B} {s : Matrix (Fin b) (Fin n) B}
    (hp : P.map φ = p) (hq : Q.map φ = q) (hr : R.map φ = r) (hs : S.map φ = s) :
    (1 + P * Q + R * S).map φ = 1 + p * q + r * s := by
  subst hp hq hr hs
  rw [Matrix.map_add _ (map_add φ), Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_mul, Matrix.map_mul]

theorem map_one_add_of_zero {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n a b : ℕ}
    (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin a) (Fin n) A) (R : Matrix (Fin n) (Fin b) A) (S : Matrix (Fin b) (Fin n) A)
    (hq : Q.map φ = 0) (hr : R.map φ = 0) : (1 + P * Q + R * S).map φ = 1 := by
  rw [map_one_add_of φ P Q R S rfl hq hr rfl, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero]

theorem matrix_ext_parts {D : D7} {n : ℕ} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    (M N : Matrix (Fin n) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hf : M.map (finPart D) = N.map (finPart D)) (hc : ∀ τ, M.map (compHom θ τ) = N.map (compHom θ τ)) : M = N := by
  ext i j
  exact adele_ext hθ (congrFun (congrFun hf i) j) fun τ => congrFun (congrFun (hc τ) i) j

theorem map_compHom_mul {D : D7} {a b c : ℕ} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau)
    (A : Matrix (Fin a) (Fin b) (AF D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin b) (Fin c) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (A * B).map (compHom θ τ) = A.map (compHom θ τ) * B.map (compHom θ τ) := Matrix.map_mul

theorem map_finPart_mul {D : D7} {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) (AF D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin b) (Fin c) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (A * B).map (finPart D) = A.map (finPart D) * B.map (finPart D) := Matrix.map_mul

theorem compHom_adMat_adj {D : D7} {m : ℕ} (τ : D.what₂.Tau) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (V : HSp D) (X : Matrix (Fin V.rank) (Fin m) D.host.E) :
    (adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (compHom θ τ) =
      (X.map (tauE D τ))ᴴ * gramAt D V τ := by
  rw [compHom_adMat τ θ hθ, Matrix.map_mul]
  congr 1
  ext i j
  exact GlobalTheory.Mem.Isom.tauE_sig D τ (X j i)

theorem exists_adelic_of_real_comps : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) {m : ℕ}
    (X : Matrix (Fin V.rank) (Fin m) D.host.E) (u : D.what₂.Tau → Matrix (Fin m) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ),
    (∀ τ, 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ) ∧
      ∃ (U : Matrix (Fin m) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
        (W : Matrix (Fin V.rank) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)),
        (∀ i v, (∀ τ, u τ i v = 0) → U i v = 0) ∧ (∀ v i, (∀ τ, w τ v i = 0) → W v i = 0) ∧
        (∀ i j, (∀ τ, (u τ * X.map (tauE D τ)) i j = 0) → (HMul.hMul U (GlobalTheory.SiegelSet.adMat D.host.F X) : Matrix (Fin m) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)) i j = 0) ∧
        (matHom V g).1 = 1 + (HMul.hMul (GlobalTheory.SiegelSet.adMat D.host.F X) U : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) +
          (HMul.hMul W (GlobalTheory.SiegelSet.adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)) : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D θ hθ V m X u w hU
  obtain ⟨-, h2⟩ := GlobalTheory.SmoothForms.RealPts.glue θ hθ V
  obtain ⟨g, hg, hgτ⟩ := h2 _ hU
  obtain ⟨U, ⟨hUf, hUc⟩, -⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ m V.rank hθ (fun τ i j => u τ i j)
  obtain ⟨W, ⟨hWf, hWc⟩, -⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ V.rank m hθ (fun τ i j => w τ i j)
  have hUc' : ∀ τ, U.map (compHom θ τ) = u τ := hUc
  have hWc' : ∀ τ, W.map (compHom θ τ) = w τ := hWc
  have hUf' : U.map (finPart D) = 0 := hUf
  have hWf' : W.map (finPart D) = 0 := hWf
  have hzero : ∀ c : AF D.host.F ⊗[D.host.F] D.host.E, finPart D c = 0 → (∀ τ, compHom θ τ c = 0) → c = 0 :=
    fun c h1 h2 => adele_ext hθ (by rw [h1, map_zero]) fun τ => by rw [h2, map_zero]
  refine ⟨g, hgτ, U, W, fun i v h => ?_, fun v i h => ?_, fun i j h => ?_, ?_⟩
  · refine hzero _ (congrFun (congrFun hUf' i) v) fun τ => ?_
    rw [← h τ, ← hUc' τ]
    rfl
  · refine hzero _ (congrFun (congrFun hWf' v) i) fun τ => ?_
    rw [← h τ, ← hWc' τ]
    rfl
  · refine hzero _ ?_ fun τ => ?_
    · have e := map_finPart_mul U (adMat D.host.F X)
      rw [hUf', Matrix.zero_mul] at e
      exact congrFun (congrFun e i) j
    · have e := map_compHom_mul θ τ U (adMat D.host.F X)
      rw [hUc', compHom_adMat τ θ hθ] at e
      rw [← h τ, ← e]
      rfl
  · have hf : (matHom V g).1.map (finPart D) = 1 := by
      have hg' : finHom V g = 1 := hg
      have e : (finHom V g).1 = (matHom V g).1.map (finPart D) := rfl
      rw [← e, hg', Units.val_one]
    refine matrix_ext_parts hθ _ _ ?_ fun τ => ?_
    · exact hf.trans (map_one_add_of_zero (finPart D) _ _ _ _ hUf' hWf').symm
    · have e := map_one_add_of (compHom θ τ) (adMat D.host.F X) U W
        (adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram))
        (compHom_adMat τ θ hθ X) (hUc' τ) (hWc' τ) (compHom_adMat_adj τ θ hθ V X)
      refine (hgτ τ).trans (Eq.trans ?_ e.symm)
      rw [Matrix.mul_assoc (w τ)]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

