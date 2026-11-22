import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0373
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetLocalComponentCopiesFixedAway
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.FinMultAway

section Abstract

variable {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
  {π : Representation ℂ G N} {ρ : Representation ℂ G X}

theorem apply_comm (φ : π.IntertwiningMap ρ) (g : G) (n : N) : φ.toLinearMap (π g n) = ρ g (φ.toLinearMap n) :=
  LinearMap.congr_fun (φ.isIntertwining' g) n

theorem isSemisimple_of_isotypic (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) : ρ.IsSemisimpleRepresentation := by
  haveI := hπ
  have hs : π.IsSemisimpleRepresentation :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule π).2 inferInstance
  exact GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range G X ρ (π.IntertwiningMap ρ) (fun _ => N) (fun _ => π)
    (fun φ => φ.toLinearMap) (fun _ => hs) (fun φ g x => apply_comm φ g x) h

theorem stable_biSup (s : Finset (π.IntertwiningMap ρ)) (g : G) :
    ∀ x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap, ρ g x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  intro x hx
  have : (⨆ φ ∈ s, LinearMap.range φ.toLinearMap) ≤ (⨆ φ ∈ s, LinearMap.range φ.toLinearMap).comap (ρ g) := by
    refine iSup₂_le fun φ hφ => ?_
    rintro _ ⟨n, rfl⟩
    rw [Submodule.mem_comap, ← apply_comm]
    exact Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ ⟨_, rfl⟩)
  exact this hx

theorem exists_intertwining_le (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) (C : Subrepresentation ρ)
    (hC : C ≠ ⊥) : ∃ ψ : π.IntertwiningMap ρ, Function.Injective ψ ∧ ∀ n, ψ n ∈ C.toSubmodule := by
  haveI := hπ
  haveI := isSemisimple_of_isotypic hπ h
  obtain ⟨C1, hc⟩ := exists_isCompl C
  have hc' : IsCompl C.toSubmodule C1.toSubmodule :=
    IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hc.inf_eq_bot)
      (congrArg Subrepresentation.toSubmodule hc.sup_eq_top)
  let P : X →ₗ[ℂ] X := C.toSubmodule.subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ hc'
  have hPl : ∀ a ∈ C.toSubmodule, P a = a := fun a ha =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc' ⟨a, ha⟩)
  have hPr : ∀ b ∈ C1.toSubmodule, P b = 0 := fun b hb =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc' ⟨b, hb⟩)
  have hPi : ∀ g x, P (ρ g x) = ρ g (P x) := fun g x => by
    have hx : x ∈ C.toSubmodule ⊔ C1.toSubmodule := by rw [hc'.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, map_add, map_add, hPl a ha, hPr b hb, hPl _ (C.apply_mem_toSubmodule g ha),
      hPr _ (C1.apply_mem_toSubmodule g hb), add_zero, add_zero]
  have hPm : ∀ x, P x ∈ C.toSubmodule := fun x => by simp [P]
  obtain ⟨c, hc0, hcne⟩ : ∃ c ∈ C.toSubmodule, c ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hC (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun x hx => hn x hx))
  by_contra hno
  push_neg at hno
  have hall : ∀ φ : π.IntertwiningMap ρ, LinearMap.range φ.toLinearMap ≤ LinearMap.ker P := by
    intro φ
    let ψ : π.IntertwiningMap ρ := ⟨P ∘ₗ φ.toLinearMap, fun g => LinearMap.ext fun n => by
      simp only [LinearMap.comp_apply]
      rw [apply_comm φ g n, hPi]⟩
    rcases Representation.IsIrreducible.injective_or_eq_zero ψ with hi | h0
    · obtain ⟨n, hn⟩ := hno ψ hi
      exact absurd (hPm _) hn
    · rintro _ ⟨n, rfl⟩
      exact DFunLike.congr_fun h0 n
  have : c ∈ LinearMap.ker P := by
    have h1 : c ∈ isoPartAlg π ρ := by rw [h]; trivial
    exact (iSup_le hall) h1
  exact hcne ((hPl c hc0).symm.trans this)

end Abstract

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

section Abstract

variable {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
  {π : Representation ℂ G N} {ρ : Representation ℂ G X}

theorem le_biSup_of_fixed (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) {v : N} (hv : v ≠ 0) (Y : Submodule ℂ X)
    (hY : ∀ g, ∀ x ∈ Y, ρ g x ∈ Y) (s : Finset (π.IntertwiningMap ρ))
    (hF : ∀ x ∈ Y, (∀ g, π g v = v → ρ g x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) :
    Y ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  haveI := isSemisimple_of_isotypic hπ h
  let A : Subrepresentation ρ := ⟨Y ⊓ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap, fun g x hx =>
    ⟨hY g x hx.1, stable_biSup s g x hx.2⟩⟩
  obtain ⟨C0, hc⟩ := exists_isCompl A
  let C : Subrepresentation ρ := ⟨Y ⊓ C0.toSubmodule, fun g x hx => ⟨hY g x hx.1, C0.apply_mem_toSubmodule g hx.2⟩⟩
  have hC : C = ⊥ := by
    by_contra hne
    obtain ⟨ψ, hi, hm⟩ := exists_intertwining_le hπ h C hne
    have hx0 : ψ v ≠ 0 := fun e => hv (hi (e.trans (map_zero ψ).symm))
    have hxY : ψ v ∈ Y := (hm v).1
    have hxM := hF _ hxY fun g hg => by rw [← ψ.isIntertwining, hg]
    have h1 : ψ v ∈ (A ⊓ C0).toSubmodule := ⟨⟨hxY, hxM⟩, (hm v).2⟩
    rw [hc.inf_eq_bot] at h1
    exact hx0 h1
  intro y hy
  have h2 : y ∈ (A ⊔ C0).toSubmodule := by rw [hc.sup_eq_top]; trivial
  obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 h2
  have hcY : c ∈ Y := by simpa using Y.sub_mem hy ha.1
  have hcC : c ∈ C.toSubmodule := ⟨hcY, hc'⟩
  rw [hC] at hcC
  have hc0 : c = 0 := hcC
  rw [hc0, add_zero]
  exact ha.2

end Abstract

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

variable {D : D7} {V : HSp D} (u : HeightOneSpectrum (𝓞 D.host.F))

theorem finLoc_locFin (x : Gv V u) : finLoc V u (locFin V u x) = x :=
  proj_emb_self D.sp.cm.sig V.gram u x

theorem commute_locFin (x : Gv V u) {k : GfC V} (hk : finLoc V u k = 1) : Commute (locFin V u x) k :=
  Subtype.ext (commute_emb D.sp.cm.sig V.gram x hk).eq

theorem continuous_finLoc : Continuous (finLoc V u) :=
  (continuous_proj D.sp.cm.sig V.gram u).comp continuous_subtype_val

theorem continuous_locFin : Continuous (locFin V u) :=
  (continuous_emb D.sp.cm.sig V.gram u).subtype_mk _

noncomputable def away : GfC V →* GfC V where
  toFun k := k * (locFin V u (finLoc V u k))⁻¹
  map_one' := by simp
  map_mul' a b := by
    have hb : finLoc V u (b * (locFin V u (finLoc V u b))⁻¹) = 1 := by
      rw [map_mul, map_inv, finLoc_locFin, mul_inv_cancel]
    have hc := (commute_locFin u (finLoc V u a) hb).inv_left
    simp only [map_mul, mul_inv_rev]
    rw [mul_assoc a _ (b * _), hc.eq]
    simp only [mul_assoc]

theorem finLoc_away (k : GfC V) : finLoc V u (away u k) = 1 := by
  show finLoc V u (k * (locFin V u (finLoc V u k))⁻¹) = 1
  rw [map_mul, map_inv, finLoc_locFin, mul_inv_cancel]

theorem away_mul (k : GfC V) : away u k * locFin V u (finLoc V u k) = k := by
  show k * (locFin V u (finLoc V u k))⁻¹ * locFin V u (finLoc V u k) = k
  group

theorem continuous_away : Continuous (away (V := V) u) :=
  continuous_id.mul (((continuous_locFin u).comp (continuous_finLoc u)).inv)

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

theorem exists_finset_fixed_away : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))), ∀ x : W, (∀ k ∈ K, finLoc V u k = 1 → σ k x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  intro D V u W _ _ σ hσa N _ _ π hπ hπa hloc K hK
  have hiso : IsIsotypicAlg π (σ.comp (locFin V u)) := hloc
  obtain ⟨v, hv⟩ : ∃ v : N, v ≠ 0 := by
    by_contra hn
    push_neg at hn
    haveI : Subsingleton N := ⟨fun a b => (hn a).trans (hn b).symm⟩
    exact (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  let St : Subgroup (Gv V u) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} ha hb => by
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        show π a⁻¹ v = v
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSt : IsOpen (St : Set (Gv V u)) := hπa.1 v
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.CuspDec.exists_compact_open V
  let K2 : Subgroup (GfC V) := K0 ⊓ St.comap (finLoc V u) ⊓ K.comap (away u)
  have hK2o : IsOpen (K2 : Set (GfC V)) :=
    (hK0o.inter (hSt.preimage (continuous_finLoc u))).inter (hK.preimage (continuous_away u))
  have hK2c : IsCompact (K2 : Set (GfC V)) :=
    hK0c.of_isClosed_subset (K2.isClosed_of_isOpen hK2o) fun k hk => hk.1.1
  haveI := hσa.2 K2 hK2o hK2c
  let Y : Submodule ℂ W := GlobalTheory.PRep.fixed σ (K ⊓ (finLoc V u).ker)
  have hmemY : ∀ x, x ∈ Y ↔ ∀ k ∈ K, finLoc V u k = 1 → σ k x = x := by
    intro x
    rw [GlobalTheory.CuspDec.mem_fixed]
    exact ⟨fun h k hk h1 => h k ⟨hk, h1⟩, fun h k hk => h k hk.1 hk.2⟩
  have hY : ∀ g, ∀ x ∈ Y, σ.comp (locFin V u) g x ∈ Y := by
    intro g x hx
    rw [hmemY] at hx ⊢
    intro k hk h1
    show σ k (σ (locFin V u g) x) = σ (locFin V u g) x
    rw [← Module.End.mul_apply, ← map_mul, ← (commute_locFin u g h1).eq, map_mul, Module.End.mul_apply, hx k hk h1]
  let F : Submodule ℂ W := Y ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) St
  have hFle : F ≤ GlobalTheory.PRep.fixed σ K2 := by
    intro y hy
    rw [GlobalTheory.CuspDec.mem_fixed]
    intro k hk
    have h1 : σ (locFin V u (finLoc V u k)) y = y := (GlobalTheory.CuspDec.mem_fixed.1 hy.2) _ hk.1.2
    have h2 : σ (away u k) y = y := (hmemY y).1 hy.1 _ hk.2 (finLoc_away u k)
    rw [← away_mul u k, map_mul, Module.End.mul_apply, h1, h2]
  haveI : FiniteDimensional ℂ F := Submodule.finiteDimensional_of_le hFle
  have hFfg : F.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ ((Submodule.fg_iff_compact F).1 hFfg)
    (fun φ : π.IntertwiningMap (σ.comp (locFin V u)) => LinearMap.range φ.toLinearMap)
    (le_of_le_of_eq le_top hiso.symm)
  refine ⟨s, fun x hx => le_biSup_of_fixed hπ hiso hv Y hY s (fun y hy hfix => hs ⟨hy, ?_⟩) ((hmemY x).2 hx)⟩
  exact GlobalTheory.CuspDec.mem_fixed.2 fun k hk => hfix k hk

end GlobalTheory.FinMultAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionalPure
section
noncomputable section

open NumberField IsDedekindDomain Filter

namespace GlobalTheory.FiniteAdelicPoints

theorem exists_functional {ι V : Type} [AddCommGroup V] [Module ℂ V] (p : ι → V) (a : ι → ℂ)
    (h : ∀ (s : Finset ι) (c : ι → ℂ), ∑ i ∈ s, c i • p i = 0 → ∑ i ∈ s, c i * a i = 0) :
    ∃ Λ : V →ₗ[ℂ] ℂ, ∀ i, Λ (p i) = a i := by
  classical

  let P : (ι →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ p
  let A : (ι →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ a

  have hk : LinearMap.ker P ≤ LinearMap.ker A := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have h0 : ∑ i ∈ c.support, c i • p i = 0 := by
      simpa [P, Finsupp.linearCombination_apply, Finsupp.sum] using hc
    simpa [A, Finsupp.linearCombination_apply, Finsupp.sum] using h c.support c h0

  let B : LinearMap.range P →ₗ[ℂ] ℂ :=
    ((LinearMap.ker P).liftQ A hk).comp (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℂ] _)
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend B
  refine ⟨Λ, fun i => ?_⟩
  have hp : P (Finsupp.single i 1) = p i := by simp [P]
  have hA : A (Finsupp.single i 1) = a i := by simp [A]
  calc Λ (p i) = Λ (P (Finsupp.single i 1)) := by rw [hp]
    _ = B ⟨P (Finsupp.single i 1), LinearMap.mem_range_self P _⟩ := by rw [← hΛ]; rfl
    _ = A (Finsupp.single i 1) := by
      simp only [B, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    _ = a i := hA

theorem sum_prod_apply {ι P : Type} {X : P → Type} [∀ v, Nonempty (X v)] (s : Finset ι) (φ : ι → ∀ v, X v → ℂ)
    (l : ∀ v, (X v → ℂ) →ₗ[ℂ] ℂ) (T : Finset P) :
    ∀ c : ι → ℂ, (∀ y : ∀ v, X v, ∑ i ∈ s, c i * ∏ v ∈ T, φ i v (y v) = 0) →
      ∑ i ∈ s, c i * ∏ v ∈ T, l v (φ i v) = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro c hc
    simpa using hc (fun v => Classical.arbitrary (X v))
  | insert w T hw ih =>
    intro c hc

    have key : ∀ y : ∀ v, X v, ∑ i ∈ s, (c i * l w (φ i w)) * ∏ v ∈ T, φ i v (y v) = 0 := by
      intro y
      have hfun : (∑ i ∈ s, (c i * ∏ v ∈ T, φ i v (y v)) • φ i w) = 0 := by
        funext t
        have hupd : ∀ i, ∏ v ∈ T, φ i v (Function.update y w t v) = ∏ v ∈ T, φ i v (y v) := fun i =>
          Finset.prod_congr rfl fun v hv => by
            rw [Function.update_of_ne (fun h => hw (by rw [← h]; exact hv))]
        have h1 := hc (Function.update y w t)
        simp only [Finset.prod_insert hw, Function.update_self, hupd] at h1
        rw [Finset.sum_apply, Pi.zero_apply, ← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring

      have h2 := congrArg (l w) hfun
      rw [map_sum, map_zero] at h2
      simp only [map_smul, smul_eq_mul] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have h3 := ih (fun i => c i * l w (φ i w)) key
    rw [← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_insert hw]
    ring

variable {F : Type} [Field F] [NumberField F]

open Classical in

def finAd (T : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) :
    FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then y v else 0, by
    filter_upwards [T.eventually_cofinite_notMem] with v hv
    simp only [hv, if_false]
    exact zero_mem _⟩

def adPt {κ : Type} (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (x : κ → mixedEmbedding.mixedSpace F)
    (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F :=
  fun k => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x k), finAd T fun v => y v k)

open Classical in

theorem pure_apply {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F))
    (hφ : ∀ v ∉ T, φ v 0 = 1) (x : κ → mixedEmbedding.mixedSpace F)
    (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ (adPt T x y) = f x * ∏ v ∈ T, φ v (y v) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure

  have h1 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (adPt T x y i)) = x := by
    funext i
    simp [adPt, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]

  have h2 : ∀ v, (fun i => GlobalTheory.AdelicU.evFin F v (adPt T x y i)) =
      fun i => if v ∈ T then y v i else (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) := fun v => by
    funext i
    rfl
  rw [h1]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [h2 v]
    simp only [if_pos hv]
  · intro v hv
    by_contra hvT
    have hvT' : v ∉ T := by simpa using hvT
    have h0 : (fun i => if v ∈ T then y v i else (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) = 0 := by
      funext i
      simp [hvT']
    rw [Function.mem_mulSupport, h2 v, h0] at hv
    exact hv (hφ v hvT')

theorem exists_functional_pure {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)
    (hvac : ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) in Filter.cofinite, vac v =
      Set.indicator {x : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | ∀ (i : κ), x i ∈ HeightOneSpectrum.adicCompletionIntegers F v}
        (1 : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ))
    (lam : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ℂ)
    (l : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (hl : Set.Finite {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | l v (vac v) ≠ 1}) :
    ∃ (Λ : ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) →ₗ[ℂ] ℂ),
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) in Filter.cofinite, φ v = vac v) →
        Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = lam f * ∏ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), l v (φ v) := by
  classical

  obtain ⟨Λ, hΛ⟩ := exists_functional
    (ι := {q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ × ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) //
      ∀ᶠ v in Filter.cofinite, q.2 v = vac v})
    (fun q => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure q.1.1 q.1.2) (fun q => lam q.1.1 * ∏ᶠ v, l v (q.1.2 v)) (by
    intro s c hc

    have f1 := Filter.eventually_cofinite.1 hvac
    have f2 := s.finite_toSet.biUnion fun q _ => Filter.eventually_cofinite.1 q.2
    let T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) := ((hl.union f1).union f2).toFinset
    have hout : ∀ v ∉ T, l v (vac v) = 1 ∧ (∀ q ∈ s, q.1.2 v = vac v) ∧ vac v 0 = 1 := by
      intro v hv
      simp only [T, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe,
        not_or, not_exists, not_not, ne_eq] at hv
      obtain ⟨⟨hv0, hv1⟩, hv2⟩ := hv
      refine ⟨hv0, fun q hq => hv2 q hq, ?_⟩
      rw [hv1]
      have hz : (0 : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈
          {x : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F v} :=
        fun i => zero_mem _
      rw [Set.indicator_of_mem hz, Pi.one_apply]

    have hrel : ∀ (x : κ → mixedEmbedding.mixedSpace F) (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v),
        ∑ q ∈ s, c q * (q.1.1 x * ∏ v ∈ T, q.1.2 v (y v)) = 0 := by
      intro x y
      have h0 := congrFun hc (adPt T x y)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [pure_apply q.1.1 q.1.2 T (fun v hv => by rw [(hout v hv).2.1 q hq, (hout v hv).2.2]) x y]

    have hrel2 : ∀ y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v,
        ∑ q ∈ s, (c q * lam q.1.1) * ∏ v ∈ T, q.1.2 v (y v) = 0 := by
      intro y
      have hz : ∑ q ∈ s, (c q * ∏ v ∈ T, q.1.2 v (y v)) • q.1.1 = 0 := by
        ext x
        simp only [sum_apply, smul_apply, smul_eq_mul, zero_apply]
        rw [← hrel x y]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
      have h0 := congrArg lam hz
      rw [map_sum, map_zero] at h0
      simp only [map_smul, smul_eq_mul] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring

    have h3 := sum_prod_apply s (fun q v => q.1.2 v) l T (fun q => c q * lam q.1.1) hrel2
    rw [← h3]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · ring
    · intro v hv
      by_contra hvT
      rw [Function.mem_mulSupport, (hout v (by simpa using hvT)).2.1 q hq] at hv
      exact hv (hout v (by simpa using hvT)).1)
  exact ⟨Λ, fun f φ hφ => hΛ ⟨(f, φ), hφ⟩⟩

end GlobalTheory.FiniteAdelicPoints

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableComplementOfIrreducibleSpanIntertwinStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners : ∀ (ι J Fm Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (τ : J → Module.End ℂ Pi) (β : Fm → Q →ₗ[ℂ] Pi),
  GlobalTheory.RealQuot.HoweCond ρ C → (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ f, C ≤ LinearMap.ker (β f)) →
  (∀ j f, ∃ f', τ j ∘ₗ β f = β f') → (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → GlobalTheory.RealQuot.IsStab τ N → N = ⊥ ∨ N = ⊤) →
  ∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N' := by
  first | exact @GlobalTheory.RealQuot.SemisimpleSpan.exists_stab_compl | exact GlobalTheory.RealQuot.SemisimpleSpan.exists_stab_compl | (intros; apply GlobalTheory.RealQuot.SemisimpleSpan.exists_stab_compl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplectiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transposeGram_coordinate_homeomorph_symplectic : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    ∃ L : WO S' T' ≃ₗ[AE D] WO S T,
      (∀ u, L u = (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) ∧
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) (AE D),
        L.symm x = ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) ∧
      Continuous L ∧ Continuous L.symm ∧ (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') ∧
      (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) ∧ ∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0 := by
  first | exact @GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | exact GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | (intros; apply GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivConjOfGramTransposeEqNegStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_equiv_conj_of_gram_transpose_eq_neg : ∀ (D : D7) (S T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank), T'.gramᵀ = -(S.gram.submatrix e₁ e₁) →
    ∃ φ' : GA D T' ≃* GA D S, Continuous φ' ∧ (∀ γ ∈ GQ T', φ' γ ∈ GQ S) ∧
      (∀ h, (Formalism.L2.Theta.mt S (φ' h)).submatrix e₁ e₁ = (Formalism.L2.Theta.mt T' h).map (cA D)) ∧
      (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) ∧ ∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det := by
  first | exact @GlobalTheory.GrpConj.exists_conj_equiv | exact GlobalTheory.GrpConj.exists_conj_equiv | (intros; apply GlobalTheory.GrpConj.exists_conj_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInvStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_equiv_inv_transpose_of_gram_inv : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  first | exact @GlobalTheory.InvTransposeIso.grp_contra | exact GlobalTheory.InvTransposeIso.grp_contra | (intros; apply GlobalTheory.InvTransposeIso.grp_contra <;> assumption)
end

