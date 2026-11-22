import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0247
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310

-- bundled from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ExistsMaximalStableAvoiding
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

section Quot

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def subRep4 (π : Representation ℂ G V) (U : Submodule ℂ V) (hU : ∀ g, ∀ v ∈ U, π g v ∈ U) :
    Representation ℂ G U where
  toFun g := (π g).restrict (fun v hv => hU g v hv)
  map_one' := LinearMap.ext fun v => Subtype.ext (by
    show π 1 (v : V) = v
    rw [map_one]; rfl)
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by
    show π (g * h) (v : V) = π g (π h v)
    rw [map_mul]; rfl)

def quotRep4 (π : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, π g v ∈ M) :
    Representation ℂ G (V ⧸ M) where
  toFun g := M.mapQ M (π g) (fun v hv => hM g v hv)
  map_one' := LinearMap.ext fun x => Submodule.Quotient.induction_on M x fun v => by
    show Submodule.Quotient.mk (π 1 v) = Submodule.Quotient.mk v
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun x => Submodule.Quotient.induction_on M x fun v => by
    show Submodule.Quotient.mk (π (g * h) v) = Submodule.Quotient.mk (π g (π h v))
    rw [map_mul]; rfl

theorem quotRep4_mk (π : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, π g v ∈ M) (g : G) (v : V) :
    quotRep4 π M hM g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π g v) := rfl

theorem exists_maximal_stable_avoiding (π : Representation ℂ G V) (x₀ : V) (hx₀ : x₀ ≠ 0) :
    ∃ M : Submodule ℂ V, (∀ g, ∀ v ∈ M, π g v ∈ M) ∧ x₀ ∉ M ∧
      ∀ N : Submodule ℂ V, (∀ g, ∀ v ∈ N, π g v ∈ N) → x₀ ∉ N → M ≤ N → N = M := by
  let S : Set (Submodule ℂ V) := {N | (∀ g, ∀ v ∈ N, π g v ∈ N) ∧ x₀ ∉ N}
  have hbot : (⊥ : Submodule ℂ V) ∈ S := ⟨fun g v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact Submodule.zero_mem _, fun h => hx₀ ((Submodule.mem_bot ℂ).1 h)⟩
  obtain ⟨M, -, hMS, hMmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨N, hN, hvN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact le_sSup hN ((hcS hN).1 g v hvN)
    · obtain ⟨N, hN, hxN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
      exact (hcS hN).2 hxN) ⊥ hbot
  exact ⟨M, hMS.1, hMS.2, fun N hN hxN hMN => le_antisymm (hMmax ⟨hN, hxN⟩ hMN) hMN⟩

theorem quotRep4_irr (π : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, π g v ∈ M) (x₀ : V)
    (hgen : ∀ N : Submodule ℂ V, (∀ g, ∀ v ∈ N, π g v ∈ N) → x₀ ∈ N → N = ⊤) (hx₀ : x₀ ∉ M)
    (hmax : ∀ N : Submodule ℂ V, (∀ g, ∀ v ∈ N, π g v ∈ N) → x₀ ∉ N → M ≤ N → N = M) :
    (quotRep4 π M hM).IsIrreducible := by
  have hne : (Submodule.Quotient.mk x₀ : V ⧸ M) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  refine { toNontrivial := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : (Submodule.Quotient.mk x₀ : V ⧸ M) ∈ (⊤ : Subrepresentation (quotRep4 π M hM)).toSubmodule :=
      Submodule.mem_top
    rw [← h] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · let N : Submodule ℂ V := S.toSubmodule.comap M.mkQ
    have hNst : ∀ g, ∀ v ∈ N, π g v ∈ N := fun g v hv => by
      show Submodule.Quotient.mk (π g v) ∈ S.toSubmodule
      rw [← quotRep4_mk π M hM]
      exact S.apply_mem_toSubmodule g hv
    by_cases hx : x₀ ∈ N
    · right
      have hN := hgen N hNst hx
      refine Subrepresentation.ext (eq_top_iff.2 fun q _ => ?_)
      induction q using Submodule.Quotient.induction_on with
      | H v =>
        have : v ∈ N := by rw [hN]; exact Submodule.mem_top
        exact this
    · left
      have hMN : M ≤ N := fun v hv => by
        show Submodule.Quotient.mk v ∈ S.toSubmodule
        rw [(Submodule.Quotient.mk_eq_zero M).2 hv]
        exact Submodule.zero_mem _
      have hN := hmax N hNst hx hMN
      refine Subrepresentation.ext (eq_bot_iff.2 fun q hq => ?_)
      induction q using Submodule.Quotient.induction_on with
      | H v =>
        have : v ∈ N := hq
        rw [hN] at this
        exact (Submodule.mem_bot ℂ).2 ((Submodule.Quotient.mk_eq_zero M).2 this)

end Quot

theorem val_unif4 {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ϖ : kˣ}
    (hϖ : ord k ϖ = 1) : valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨π₀, hπ₀⟩ := exists_uniformizer k
  have h1 : ord k π₀ = 1 := ord_eq_one hπ₀
  have h0 : ord k π₀⁻¹ = -1 := by
    have := ord_mul k π₀ π₀⁻¹
    rw [mul_inv_cancel, ord_eq_zero (by simp), h1] at this
    omega
  have h2 : ord k (ϖ * π₀⁻¹) = 0 := by rw [ord_mul, h0, hϖ]; norm_num
  have h3 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀] at h3
  have hne : valuation k (π₀ : k) ≠ 0 := by simp
  rw [mul_inv_eq_one₀ hne] at h3
  rw [h3, hπ₀]

theorem st4 : St4 := by
  intro k W _ _ _ _ _ _ _ n hn τ hτ ϖ hϖ c
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨ω₀, hω₀⟩ := exists_hasCentralChar hτ
  obtain ⟨ω, hω, hωc⟩ := exists_isTameLift ω₀ (val_unif4 hϖ) c
  have hE : ExtendsCentral ω τ := hω.extendsCentral hω₀
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, w₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI := hτ
    exact (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤) (Subrepresentation.ext (Submodule.ext fun w => by
      rw [hcon w]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩))
  let π₀ := depthZero τ ω hE
  let cn := canon τ ω hE
  have hcn : ∀ (g : KO k (Fin n)) (w : W), cn (τ (redK k (Fin n) g) w) = π₀ g (cn w) := fun g w => by
    rw [← extZK_KO τ ω hE, (canon τ ω hE).isIntertwining]; rfl
  let x₀ := cn w₀
  have hx₀ : x₀ ≠ 0 := fun h => hw₀ (canon_injective τ ω hE (h.trans (map_zero _).symm))
  let U : Submodule ℂ (DepthZeroSp τ ω hE) := Submodule.span ℂ (Set.range fun g => π₀ g x₀)
  have hU : ∀ g, ∀ v ∈ U, π₀ g v ∈ U := fun g v hv => by
    have hle : U ≤ U.comap (π₀ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp only [map_mul, Module.End.mul_apply]⟩)
    exact hle hv
  have hx₀U : x₀ ∈ U := Submodule.subset_span ⟨1, by simp only [map_one, Module.End.one_apply]⟩
  have hcnU : ∀ w, cn w ∈ U := by
    let S : Subrepresentation τ := ⟨U.comap cn.toLinearMap, fun g v hv => by
      obtain ⟨g', rfl⟩ := redK_surjective g
      show cn _ ∈ U
      rw [hcn]
      exact hU g' _ hv⟩
    have hS : S = ⊤ := by
      refine (hτ.eq_bot_or_eq_top S).resolve_left fun h => hw₀ ?_
      have : w₀ ∈ S.toSubmodule := hx₀U
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    intro w
    have : w ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
    exact this
  let π₁ := subRep4 π₀ U hU
  let x₁ : U := ⟨x₀, hx₀U⟩
  have hx₁ : x₁ ≠ 0 := fun h => hx₀ (congrArg Subtype.val h)
  have hgen : ∀ N : Submodule ℂ U, (∀ g, ∀ v ∈ N, π₁ g v ∈ N) → x₁ ∈ N → N = ⊤ := by
    intro N hN hxN
    have hle : U ≤ N.map U.subtype := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      exact ⟨π₁ g x₁, hN g x₁ hxN, rfl⟩)
    refine eq_top_iff.2 fun u _ => ?_
    obtain ⟨u', hu', he⟩ := hle u.2
    rwa [show u' = u from Subtype.ext he] at hu'
  obtain ⟨M, hM, hx₁M, hMmax⟩ := exists_maximal_stable_avoiding π₁ x₁ hx₁
  let ρQ := quotRep4 π₁ M hM
  have hirr : ρQ.IsIrreducible := quotRep4_irr π₁ M hM x₁ hgen hx₁M hMmax
  have hsm : IsSmooth ρQ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      let H : Subgroup (GL (Fin n) k) :=
        { carrier := {g | ρQ g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u}
          one_mem' := by simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply]
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
            rw [hb, ha]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq] at ha ⊢
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      have hopen : IsOpen {g : GL (Fin n) k | π₀ g (u : DepthZeroSp τ ω hE) = u} := isSmooth_depthZero τ ω hE u
      have hsub : {g : GL (Fin n) k | π₀ g (u : DepthZeroSp τ ω hE) = u} ⊆ (H : Set (GL (Fin n) k)) := fun g hg => by
        show ρQ g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
        rw [quotRep4_mk]
        congr 1
        exact Subtype.ext hg
      exact Subgroup.isOpen_of_mem_nhds H (g := 1)
        (Filter.mem_of_superset (hopen.mem_nhds (by simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply])) hsub)
  let jU : W →ₗ[ℂ] U := LinearMap.codRestrict U cn.toLinearMap hcnU
  let j : W →ₗ[ℂ] (U ⧸ M) := M.mkQ.comp jU
  have hj : ∀ (g : KO k (Fin n)) (v : W), j (τ (redK k (Fin n) g) v) = ρQ g (j v) := fun g v => by
    show Submodule.Quotient.mk (jU (τ (redK k (Fin n) g) v)) = Submodule.Quotient.mk (π₁ g (jU v))
    congr 1
    exact Subtype.ext (hcn g v)
  have hjinj : Function.Injective j := by
    let K : Subrepresentation τ := ⟨LinearMap.ker j, fun g v hv => by
      obtain ⟨g', rfl⟩ := redK_surjective g
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hj, hv, map_zero]⟩
    have hK : K = ⊥ := by
      refine (hτ.eq_bot_or_eq_top K).resolve_right fun h => ?_
      have : w₀ ∈ K.toSubmodule := by rw [h]; exact Submodule.mem_top
      have h2 : j w₀ = 0 := LinearMap.mem_ker.1 this
      apply hx₁M
      exact (Submodule.Quotient.mk_eq_zero M).1 h2
    have : LinearMap.ker j = ⊥ := congrArg Subrepresentation.toSubmodule hK
    exact LinearMap.ker_eq_bot.1 this
  refine ⟨⟨U ⧸ M, ρQ, hsm, hirr⟩, ω, j, ?_, hωc, hjinj, hj⟩
  intro z q
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    show ρQ (GeneralLinearGroup.scalar (Fin n) z) (Submodule.Quotient.mk u) = (ω z : ℂ) • Submodule.Quotient.mk u
    rw [quotRep4_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hasCentralChar_depthZero τ ω hE z u)

end PositivityTheory.Rg.DzCount

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.FiniteCuspidalOfIsCuspidal
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

private theorem exists_block_lt_unipotent_lemma {K : Type} [Field K] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) {g : GL (Fin n) K} (hg : g ∈ GlobalTheory.SmGL.unipRad K e) (i j : Fin n)
    (hij : GlobalTheory.SmGL.blk e i = GlobalTheory.SmGL.blk e j) :
    (g : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0 := by
  obtain ⟨⟨y, hy⟩, hk, rfl⟩ := Subgroup.mem_map.1 hg
  rw [MonoidHom.mem_ker] at hk
  obtain ⟨a, i', hi⟩ : ∃ a i', e.symm i = ⟨a, i'⟩ := ⟨_, _, rfl⟩
  obtain ⟨b, j', hj⟩ : ∃ b j', e.symm j = ⟨b, j'⟩ := ⟨_, _, rfl⟩
  have hab : a = b := by
    simp only [GlobalTheory.SmGL.blk, hi, hj] at hij
    exact hij
  subst hab
  have hi2 : i = e ⟨a, i'⟩ := by
    rw [← hi, Equiv.apply_symm_apply]
  have hj2 : j = e ⟨a, j'⟩ := by
    rw [← hj, Equiv.apply_symm_apply]
  have h3 := congrArg (fun u => ((u a : GL (Fin (d a)) K) : Matrix (Fin (d a)) (Fin (d a)) K) i' j') hk
  simp [GlobalTheory.SmGL.leviProj, GlobalTheory.SmGL.diagBlock, Matrix.one_apply] at h3
  subst hi2 hj2
  simp [h3]

theorem exists_block_lt_unipotent {K : Type} [Field K] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) (h : GlobalTheory.SmGL.unipRad K e ≠ ⊥) :
    ∃ i j : Fin n, GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := by
  by_contra hcon
  push_neg at hcon
  apply h
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [exists_block_lt_unipotent_lemma e hg i j (le_antisymm (hcon j i) (hcon i j))]
  simp [Matrix.one_apply]

private theorem finite_cuspidal_of_isCuspidal_lemma {K : Type} [Field K] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) (g : GL (Fin n) K)
    (h1 : (g : Matrix (Fin n) (Fin n) K).BlockTriangular (GlobalTheory.SmGL.blk e))
    (h2 : ∀ i j, GlobalTheory.SmGL.blk e i = GlobalTheory.SmGL.blk e j → (g : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0) :
    g ∈ GlobalTheory.SmGL.unipRad K e := by
  refine Subgroup.mem_map.2 ⟨⟨g, h1⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  funext a
  refine Units.ext ?_
  ext i' j'
  have h3 := h2 (e ⟨a, i'⟩) (e ⟨a, j'⟩) (by simp [GlobalTheory.SmGL.blk])
  simp [GlobalTheory.SmGL.leviProj, GlobalTheory.SmGL.diagBlock, Matrix.one_apply, h3]

private theorem finite_cuspidal_of_isCuspidal_lemma_2 {K : Type} [Field K] [Fintype K] [DecidableEq K] {n s : ℕ}
    {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s) (u : GL (Fin n) K)
    (hu : u ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (fun i => if GlobalTheory.SmGL.blk e i < t then (0 : Fin 2) else 1)) :
    u ∈ GlobalTheory.SmGL.unipRad K e := by
  obtain ⟨⟨hut, -⟩, hud⟩ := hu
  refine finite_cuspidal_of_isCuspidal_lemma e u ?_ ?_
  · intro i j hji
    by_cases hb : (if GlobalTheory.SmGL.blk e j < t then (0 : Fin 2) else 1) <
        (if GlobalTheory.SmGL.blk e i < t then (0 : Fin 2) else 1)
    · exact hut i j hb
    · have hne : i ≠ j := by
        intro h
        subst h
        exact lt_irrefl _ hji
      rw [hud i j ?_, if_neg hne]
      by_cases h1 : GlobalTheory.SmGL.blk e i < t
      · have h2 : GlobalTheory.SmGL.blk e j < t := lt_trans hji h1
        simp [h1, h2]
      · by_cases h2 : GlobalTheory.SmGL.blk e j < t
        · simp [h1, h2] at hb
        · simp [h1, h2]
  · intro i j hij
    rw [hud i j (by simp [hij])]

theorem finite_cuspidal_of_isCuspidal {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}
    (τ : FDRep ℂ (GL (Fin n) K)) (h : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ) : FinCusp τ.ρ := by
  unfold FinCusp
  intro s d e hne v hv
  obtain ⟨i0, j0, hlt⟩ := exists_block_lt_unipotent e hne
  refine h 2 (fun i => if GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j0 then 0 else 1) ?_ le_rfl v ?_
  · intro k
    fin_cases k
    · exact ⟨i0, by simp [hlt]⟩
    · exact ⟨j0, by simp⟩
  · intro u hu
    exact hv u (finite_cuspidal_of_isCuspidal_lemma_2 e _ u hu)

theorem hasCuspLabel_of_equiv {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K) {n : ℕ} {τ τ' : FDRep ℂ (GL (Fin n) K)} (e : τ ≃ₗ[ℂ] τ')
    (he : ∀ g v, e (τ.ρ g v) = τ'.ρ g (e v)) {P : K[X]} (h : Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ P) :
    Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ' P := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun x hx γ hγ z hz m hm => ?_⟩
  rw [← h5 x hx γ hγ z hz m hm]
  have hc : τ'.ρ γ = (e.toLinearMap ∘ₗ τ.ρ γ) ∘ₗ e.symm.toLinearMap := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearEquiv.apply_symm_apply]
  rw [hc, ← LinearEquiv.conj_apply, LinearMap.trace_conj']

theorem st7 : St7 := by
  intro K _ _ n hn
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨C⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.nonempty_labelConv K
  obtain ⟨P0, a0, b0, c0, d0⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.exists_monic_irreducible K n hn
  obtain ⟨τ0, -⟩ := GlobalTheory.T.exists_cuspidal_with_label K C n hn P0 a0 b0 c0 d0
  have hex : ∀ P : K[X], ∃ τ : FDRep ℂ (GL (Fin n) K), P ∈ Lab K n →
      CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ P := by
    intro P
    by_cases hP : P ∈ Lab K n
    · obtain ⟨p1, p2, p3, p4⟩ := hP
      obtain ⟨τ, hs, hc, hl⟩ := GlobalTheory.T.exists_cuspidal_with_label K C n hn P p1 p2 p3 p4
      exact ⟨τ, fun _ => ⟨hs, hc, hl⟩⟩
    · exact ⟨τ0, fun h' => absurd h' hP⟩
  choose τ hτ using hex
  refine ⟨τ, fun P hP => ⟨GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple _ (hτ P hP).1,
    finite_cuspidal_of_isCuspidal _ (hτ P hP).2.1⟩, ?_⟩
  rintro P hP P' hP' ⟨e, he⟩
  exact GlobalTheory.T.cuspidal_label_unique K C (Fin n) (τ P') P P' (hasCuspLabel_of_equiv C e he (hτ P hP).2.2)
    (hτ P' hP').2.2

end PositivityTheory.Rg.DzCount

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.HasCentralCharOfEquiv
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace CentralCharacterTransfer

theorem equiv_apply {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ (ρ g v) = σ g (φ v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H : Subgroup G} {v : V} : v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  change (∀ h : H, ρ h v = ((1 : H →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro hv h hh
    exact hv ⟨h, hh⟩
  · intro hv h
    exact hv h h.2

theorem map_fixed {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (H : Subgroup G) :
    (fixed ρ H).map φ.toLinearEquiv.toLinearMap = fixed σ H := by
  ext w
  simp only [Submodule.mem_map, mem_fixed_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ h hh
    change σ h (φ v) = φ v
    rw [← equiv_apply, hv h hh]
  · intro hw
    have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
    refine ⟨φ.toLinearEquiv.symm w, fun h hh => ?_, e2⟩
    apply φ.toLinearEquiv.injective
    change φ _ = φ _
    rw [equiv_apply, e2, hw h hh]

theorem hasCentralChar_of_equiv {k V W : Type} [Field k] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv σ)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) : HasCentralChar σ ω := by
  intro z w
  have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
  rw [← e2, ← equiv_apply, h z]
  exact φ.toLinearEquiv.map_smul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem transfer {W W' V V' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}
    {τ : Representation ℂ (GL (Fin n) 𝓀[k]) W} {τ' : Representation ℂ (GL (Fin n) 𝓀[k]) W'}
    {π : Representation ℂ (GL (Fin n) k) V} {π' : Representation ℂ (GL (Fin n) k) V'}
    {j : W →ₗ[ℂ] V} {j' : W' →ₗ[ℂ] V'} (hj : IsTypeMap τ π j) (hj' : IsTypeMap τ' π' j')
    (hf : fixed π (KOne k (Fin n)) = LinearMap.range j) (hf' : fixed π' (KOne k (Fin n)) = LinearMap.range j')
    (φ : π.Equiv π') : ∃ e : W ≃ₗ[ℂ] W', ∀ g v, e (τ g v) = τ' g (e v) := by
  have hm := map_fixed φ (KOne k (Fin n))
  rw [hf, hf'] at hm
  let e : W ≃ₗ[ℂ] W' := (LinearEquiv.ofInjective j hj.1).trans
    ((φ.toLinearEquiv.submoduleMap (LinearMap.range j)).trans
      ((LinearEquiv.ofEq _ _ hm).trans (LinearEquiv.ofInjective j' hj'.1).symm))
  have key : ∀ w, j' (e w) = φ (j w) := by
    intro w
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective j' hj'.1).apply_symm_apply
      ((LinearEquiv.ofEq _ _ hm) ((φ.toLinearEquiv.submoduleMap _) ((LinearEquiv.ofInjective j hj.1) w))))
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  refine ⟨e, fun g v => ?_⟩
  obtain ⟨g', rfl⟩ := GlobalTheory.LocGL.redK_surjective g
  apply hj'.1
  rw [key, hj.2, hj'.2, key]
  exact equiv_apply φ _ _

end CentralCharacterTransfer

open CentralCharacterTransfer in
theorem st8a : St4 → St5 → St6 → St7 → St8a := by
  classical
  intro h4 h5 h6 h7 k _ _ _ _ n hn ϖ hϖ c
  obtain ⟨τ, hτ, hinj⟩ := h7 𝓀[k] n hn
  have hdata : ∀ P ∈ Lab 𝓀[k] n, ∃ (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (j : (τ P).V →ₗ[ℂ] π.V),
      HasCentralChar π.ρ ω ∧ ω ϖ = c ∧ IsTypeMap (τ P).ρ π.ρ j :=
    fun P hP => h4 k (τ P).V n hn (τ P).ρ (hτ P hP).1 ϖ hϖ c
  choose π ω j hω hc hj using hdata
  have hirr : (1 : Representation ℂ (GL (Fin n) k) ℂ).IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun s => ?_ }
    · exact bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule h)
    · rcases Ideal.eq_bot_or_top s.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  let d : IrrRep (GL (Fin n) k) := ⟨ℂ, 1, fun v => by simp, hirr⟩
  let F : 𝓀[k][X] → IrrGL k := fun P =>
    if hP : P ∈ Lab 𝓀[k] n then ⟨n, Quotient.mk _ (π P hP)⟩ else ⟨n, Quotient.mk _ d⟩
  have hF : ∀ P (hP : P ∈ Lab 𝓀[k] n), F P = ⟨n, Quotient.mk _ (π P hP)⟩ := by
    intro P hP
    simp only [F, dif_pos hP]
  have hfix : ∀ P (hP : P ∈ Lab 𝓀[k] n),
      fixed (π P hP).ρ (KOne k (Fin n)) = LinearMap.range (j P hP) := by
    intro P hP
    haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    exact h6 k (τ P).V n (τ P).ρ (hτ P hP).2 (π P hP) (ω P hP) (hω P hP) (j P hP) (hj P hP)
  refine ⟨F, fun P hP => ?_, fun P hP P' hP' hPP => ?_⟩
  · haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    rw [hF P hP]
    obtain ⟨ψ⟩ : Nonempty ((π P hP).ρ.Equiv
        (IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).ρ) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).symm
    set π₀ := IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))
    let j₀ : (τ P).V →ₗ[ℂ] π₀.V := ψ.toLinearEquiv.toLinearMap ∘ₗ j P hP
    have hj₀ : IsTypeMap (τ P).ρ π₀.ρ j₀ := by
      refine ⟨ψ.toLinearEquiv.injective.comp (hj P hP).1, fun g v => ?_⟩
      change ψ (j P hP _) = π₀.ρ g (ψ (j P hP v))
      rw [(hj P hP).2, equiv_apply]
    have hcc := hasCentralChar_of_equiv ψ (hω P hP)
    refine ⟨rfl, ⟨hn, h5 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ j₀ hj₀⟩, ?_, ω P hP, hcc, hc P hP⟩
    change fixed π₀.ρ (KOne k (Fin n)) ≠ ⊥
    rw [h6 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ (ω P hP) hcc j₀ hj₀]
    obtain ⟨w, hw⟩ := exists_ne (0 : (τ P).V)
    intro hb
    apply hw
    apply hj₀.1
    rw [map_zero]
    have hm : j₀ w ∈ LinearMap.range j₀ := LinearMap.mem_range_self j₀ w
    rw [hb] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · rw [hF P hP, hF P' hP'] at hPP
    have hq := eq_of_heq (Sigma.mk.inj_iff.1 hPP).2
    obtain ⟨φ⟩ : Nonempty ((π P hP).ρ.Equiv (π P' hP').ρ) := Quotient.exact hq
    obtain ⟨e, he⟩ := transfer (hj P hP) (hj P' hP') (hfix P hP) (hfix P' hP') φ
    exact hinj P hP P' hP' ⟨e, he⟩

end PositivityTheory.Rg.DzCount

end
end

