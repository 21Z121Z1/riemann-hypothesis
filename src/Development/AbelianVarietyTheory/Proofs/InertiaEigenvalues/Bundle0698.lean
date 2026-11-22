import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParameters
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL.SphUniq

section Abstract

variable {G X V V' : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']

theorem map_eq_top {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hπ : π.IsIrreducible)
    (f : ρ.IntertwiningMap π) (U : Submodule ℂ X) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) {u : X} (hu : u ∈ U)
    (h0 : f u ≠ 0) (v : V) : ∃ x ∈ U, f x = v := by
  let R : Subrepresentation π := ⟨U.map f.toLinearMap, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, hU g x hx, f.isIntertwining _ _ g x⟩⟩
  rcases eq_bot_or_eq_top R with h | h
  · have h1 : f u ∈ R.toSubmodule := ⟨u, hu, rfl⟩
    rw [h] at h1
    exact absurd h1 h0
  · have h1 : v ∈ R.toSubmodule := by rw [h]; trivial
    exact h1

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem ker_le {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (f : ρ.IntertwiningMap π) (f' : ρ.IntertwiningMap π') {w : X} (hw : w ∈ fixed ρ K) (h0 : f w ≠ 0)
    (h0' : f' w ≠ 0) (hl : ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • w) :
    LinearMap.ker f.toLinearMap ≤ LinearMap.ker f'.toLinearMap := by
  intro u hu
  by_contra hu'
  obtain ⟨x, hx, e⟩ := map_eq_top hπ' f' (LinearMap.ker f.toLinearMap) (fun g y hy => by
    have hy' : f y = 0 := hy
    show f (ρ g y) = 0
    rw [f.isIntertwining, hy', map_zero]) hu hu' (f' w)
  have hx' : f x = 0 := hx
  obtain ⟨v, hv, ev⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK (f.toLinearMap.prod f'.toLinearMap) x fun g hg => by
    have h1 : ρ g w = w := by simpa using hw ⟨g, hg⟩
    refine Prod.ext ?_ ?_
    · show f (ρ g x) = f x
      rw [f.isIntertwining, hx', map_zero]
    · show f' (ρ g x) = f' x
      rw [f'.isIntertwining, e, ← f'.isIntertwining, h1]
  obtain ⟨c, rfl⟩ := hl v hv
  have e1 : f (c • w) = f x := congrArg Prod.fst ev
  have e2 : f' (c • w) = f' x := congrArg Prod.snd ev
  rw [hx', map_smul, smul_eq_zero] at e1
  rw [e1.resolve_right h0, zero_smul, map_zero, e] at e2
  exact h0' e2.symm

theorem equiv_of_line {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (f : ρ.IntertwiningMap π) (f' : ρ.IntertwiningMap π') {w : X} (hw : w ∈ fixed ρ K) (h0 : f w ≠ 0)
    (h0' : f' w ≠ 0) (hl : ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • w) : Nonempty (π.Equiv π') := by
  have hk := le_antisymm (ker_le hρ hπ' hK f f' hw h0 h0' hl) (ker_le hρ hπ hK f' f hw h0' h0 hl)
  have hs : Function.Surjective f.toLinearMap := fun v => by
    obtain ⟨x, -, e⟩ := map_eq_top hπ f ⊤ (fun _ _ _ => trivial) trivial h0 v
    exact ⟨x, e⟩
  have hs' : Function.Surjective f'.toLinearMap := fun v => by
    obtain ⟨x, -, e⟩ := map_eq_top hπ' f' ⊤ (fun _ _ _ => trivial) trivial h0' v
    exact ⟨x, e⟩
  let L : V ≃ₗ[ℂ] V' := (f.toLinearMap.quotKerEquivOfSurjective hs).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    f'.toLinearMap.quotKerEquivOfSurjective hs'
  have hL : ∀ x, L (f x) = f' x := fun x => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hs).symm (f x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [L, LinearEquiv.trans_apply, this]
    rfl
  refine ⟨Representation.Equiv.mk L fun g => LinearMap.ext fun v => ?_⟩
  obtain ⟨x, rfl⟩ := hs v
  show L (π g (f x)) = π' g (L (f x))
  rw [← f.isIntertwining, hL, hL, f'.isIntertwining]

theorem exists_vector {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap π)
    (hf : Function.Surjective f) (hs : fixed π K ≠ ⊥) :
    ∃ w : S.toSubmodule, w.1 ∈ fixed ρ K ∧ f w ≠ 0 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  have hS : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨S, .id _, Function.surjective_id⟩ hρ
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hS hK f.toLinearMap u fun h hh => by
    show f (S.toRepresentation h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  exact ⟨w, fun g => congrArg Subtype.val (hw g), fun h => hv0 (hfw.symm.trans h)⟩

theorem equiv_of_form {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (E : X →ₗ[ℂ] ℂ) (hE : ∀ u ∈ fixed ρ K, E u = 0 → u = 0) (h : IsSubquotient π ρ) (h' : IsSubquotient π' ρ)
    (hs : fixed π K ≠ ⊥) (hs' : fixed π' K ≠ ⊥) : Nonempty (π.Equiv π') := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨S', f', hf'⟩ := h'
  obtain ⟨w, hw, h0⟩ := exists_vector hρ hK S f hf hs
  obtain ⟨w', hw', h0'⟩ := exists_vector hρ hK S' f' hf' hs'
  have hl : ∀ z ∈ fixed ρ K, z ≠ 0 → ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • z := fun z hz hz0 v hv => by
    have hEz : E z ≠ 0 := fun e => hz0 (hE z hz e)
    refine ⟨E v / E z, sub_eq_zero.1 (hE _ (sub_mem hv (Submodule.smul_mem _ _ hz)) ?_)⟩
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hEz, sub_self]
  have hw0 : w.1 ≠ 0 := fun e => h0 (by rw [show w = 0 from Subtype.ext e, map_zero])
  have hw0' : w'.1 ≠ 0 := fun e => h0' (by rw [show w' = 0 from Subtype.ext e, map_zero])
  obtain ⟨c, hc⟩ := hl _ hw' hw0' _ hw
  have hc0 : c ≠ 0 := fun e => hw0 (by rw [hc, e, zero_smul])
  let R : Subrepresentation ρ := ⟨S.toSubmodule ⊓ S'.toSubmodule, fun g _ hv =>
    ⟨S.apply_mem_toSubmodule g hv.1, S'.apply_mem_toSubmodule g hv.2⟩⟩
  have hR : IsSmooth R.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨R, .id _, Function.surjective_id⟩ hρ
  let F : R.toRepresentation.IntertwiningMap π :=
    ⟨f.toLinearMap ∘ₗ Submodule.inclusion inf_le_left, fun g => LinearMap.ext fun x =>
      f.isIntertwining _ _ g (Submodule.inclusion inf_le_left x)⟩
  let F' : R.toRepresentation.IntertwiningMap π' :=
    ⟨f'.toLinearMap ∘ₗ Submodule.inclusion inf_le_right, fun g => LinearMap.ext fun x =>
      f'.isIntertwining _ _ g (Submodule.inclusion inf_le_right x)⟩
  have hm : w.1 ∈ S'.toSubmodule := hc ▸ Submodule.smul_mem _ _ w'.2
  refine equiv_of_line hR hπ hπ' hK F F' (w := ⟨w.1, w.2, hm⟩) (fun g => Subtype.ext (hw g)) h0 (fun e => ?_)
    fun v hv => ?_
  · have e1 : f' (c • w') = 0 := by
      rw [← e]
      exact congrArg f' (Subtype.ext hc.symm)
    rw [map_smul, smul_eq_zero] at e1
    exact e1.elim hc0 h0'
  · obtain ⟨d, hd⟩ := hl _ hw hw0 v.1 fun g => congrArg Subtype.val (hv g)
    exact ⟨d, Subtype.ext hd⟩

end Abstract

theorem equiv_of_parInd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (σ : Representation ℂ (Levi k m) ℂ)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (GL n k) V} {π' : Representation ℂ (GL n k) V'}
    (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) (h : IsSubquotient π (parInd e σ))
    (h' : IsSubquotient π' (parInd e σ)) (hs : IsSpherical π) (hs' : IsSpherical π') : Nonempty (π.Equiv π') := by
  let E : IndSp e σ →ₗ[ℂ] ℂ := ⟨⟨fun f => f.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  refine equiv_of_form (isSmooth_parInd e σ) hπ hπ' SplitFlip.isCompact_KO E (fun u hu h0 => ?_) h h' hs hs'
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  have h1 := congrArg (fun F : IndSp e σ => F.1.1 1) (hu ⟨c, hc⟩)
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul, one_mul] at h1
  have h2 : u.1.1 1 = 0 := h0
  rw [parInd_law, h1, h2, map_zero, smul_zero]
  rfl

theorem equiv_of_hasSatake : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (α : Fin n → ℂˣ) (π π' : IrrRep (GL (Fin n) k)), HasSatake π.ρ α → HasSatake π'.ρ α → Nonempty (π.ρ.Equiv π'.ρ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ h h' => equiv_of_parInd _ _ h.1 h'.1 h.2.2 h'.2.2 h.2.1 h'.2.1

end GlobalTheory.SmGL.SphUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalUnitaryLagrangianActionEqOfMemFrameUnipo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCuspStab

open GlobalTheory.MixModel GlobalTheory.RallisCusp

variable {D : D7}

theorem inv_fix {n s : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (M : Matrix (Fin n) (Fin s) (AE D))
    (hBA : B * A = 1) (h : A ⬝ M = M) : B ⬝ M = M := by
  calc B ⬝ M = B ⬝ (A ⬝ M) := by rw [h]
    _ = M := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]

theorem inv_sub_one {n : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (hBA : B * A = 1) : B - 1 = -(B * (A - 1)) := by
  rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]

set_option maxHeartbeats 1000000 in

theorem ni_prop (W : HSp D) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E) (g : GA D W) (hg : g ∈ NI W I) :
    Formalism.L2.Theta.mt W g ⬝ I.map (incA D) = I.map (incA D) ∧
    ∀ x : Fin W.rank → D.host.E, (Iᴴ * W.gram) *ᵥ x = 0 →
      ∃ a : Fin s → AE D, (Formalism.L2.Theta.mt W g - 1) *ᵥ (fun i => incA D (x i)) = I.map (incA D) *ᵥ a := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    refine ⟨?_, fun x hx => hg.2.2 x hx⟩
    have h1 : (Formalism.L2.Theta.mt W g - 1) ⬝ I.map (incA D) = 0 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one =>
    refine ⟨by rw [GlobalTheory.MixModel.mt_one, Matrix.one_mul], fun x _ => ⟨0, ?_⟩⟩
    rw [GlobalTheory.MixModel.mt_one, sub_self, Matrix.zero_mulVec, Matrix.mulVec_zero]
  | mul x y _ _ hx hy =>
    refine ⟨by rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, hy.1, hx.1], fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hx.2 v hv
    obtain ⟨b, hb⟩ := hy.2 v hv
    refine ⟨b + a, ?_⟩
    have e : Formalism.L2.Theta.mt W (x * y) - 1 =
        Formalism.L2.Theta.mt W x * (Formalism.L2.Theta.mt W y - 1) + (Formalism.L2.Theta.mt W x - 1) := by
      rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hb, ha, Matrix.mulVec_mulVec, hx.1, Matrix.mulVec_add]
  | inv x _ hx =>
    obtain ⟨hx1, hx2⟩ := hx
    have hinv := inv_fix _ _ _ (GlobalTheory.MixModel.mt_inv_mul W x) hx1
    refine ⟨hinv, fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hx2 v hv
    refine ⟨-a, ?_⟩
    rw [inv_sub_one _ _ (GlobalTheory.MixModel.mt_inv_mul W x), Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, hinv, Matrix.mulVec_neg]

theorem exists_leftInv {m s : ℕ} (I : Matrix (Fin m) (Fin s) D.host.E) (hI : LinearIndependent D.host.E I.transpose) :
    ∃ L : Matrix (Fin s) (Fin m) D.host.E, L * I = 1 := by
  have hB : Function.Injective I.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    exact hI
  have hker : LinearMap.ker (Matrix.toLin' I) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact hB (by simpa [Matrix.toLin'_apply] using h)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' I) hker
  exact ⟨LinearMap.toMatrix' g, by
    rw [← LinearMap.toMatrix'_toLin' I, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]⟩

theorem descend {m s : ℕ} (I : Matrix (Fin m) (Fin s) D.host.E) (hI : LinearIndependent D.host.E I.transpose)
    (v : Fin m → D.host.E) (a : Fin s → AE D) (h : (fun i => incA D (v i)) = I.map (incA D) *ᵥ a) :
    ∃ b : Fin s → D.host.E, v = I *ᵥ b := by
  obtain ⟨L, hL⟩ := exists_leftInv I hI
  refine ⟨L *ᵥ v, ?_⟩
  have ha : a = fun j => incA D ((L *ᵥ v) j) := by
    have h1 : L.map (incA D) *ᵥ (fun i => incA D (v i)) = a := by
      rw [h, Matrix.mulVec_mulVec, ← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rw [← h1]
    funext j
    exact (RingHom.map_mulVec (incA D) L v j).symm
  funext i
  apply incA_injective
  have := congrFun h i
  rw [this, ha]
  exact (RingHom.map_mulVec (incA D) I (L *ᵥ v) i).symm

theorem fst_perp (W : HSp D) (Y : Lag W) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E)
    (hY : Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _))
    (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) (hy : y ∈ Y.1) : (Iᴴ * W.gram) *ᵥ y.1 = 0 := by
  funext a
  have hcol : ((I.transpose a, 0) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ∈ Y.1 := by
    have h : I.transpose a ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := hY ▸ Submodule.subset_span ⟨a, rfl⟩
    exact h
  have hiso := Y.2.2 _ hcol y hy
  simp only [star_zero, zero_dotProduct] at hiso
  rw [← Matrix.mulVec_mulVec]
  show _ = (0 : D.host.E)
  rw [← hiso]
  rfl

theorem lagAct_eq_of_mem_NI : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E),
    IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) →
    ∀ n : GQ W, (n : GA D W) ∈ NI W I → GlobalTheory.RallisCusp.lagAct W n Y = Y := by
  intro D W Y s I hI hY n hn
  have hn' : ((n⁻¹ : GQ W) : GA D W) ∈ NI W I := by
    rw [InvMemClass.coe_inv]
    exact inv_mem hn
  obtain ⟨-, hP⟩ := ni_prop W I _ hn'
  have hc : Formalism.L2.Theta.mt W ((n⁻¹ : GQ W) : GA D W) - 1 = (gqMat W n⁻¹ - 1).map (incA D) := by
    rw [← rat_gqMat, ← rat_one, ← rat_sub]
    rfl
  have hle : Y.1 ≤ (lagAct W n Y).1 := by
    intro y hy
    rw [mem_lagAct]
    obtain ⟨a, ha⟩ := hP y.1 (fst_perp W Y I hY y hy)
    obtain ⟨b, hb⟩ := descend I hI.2.1 ((gqMat W n⁻¹ - 1) *ᵥ y.1) a (by
      rw [← ha, hc]
      funext i
      exact RingHom.map_mulVec (incA D) _ _ i)
    have hIb : ((I *ᵥ b, 0) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ∈ Y.1 := by
      have h : I *ᵥ b ∈ Submodule.span D.host.E (Set.range I.col) := by
        rw [← Matrix.range_mulVecLin]
        exact ⟨b, rfl⟩
      have h' : I *ᵥ b ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := by
        rw [← hY]
        exact h
      exact h'
    have e : ((gqMat W n⁻¹ *ᵥ y.1, y.2) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) =
        y + (I *ᵥ b, 0) := by
      rw [← hb, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact Prod.ext (by simp) (by simp)
    rw [e]
    exact Y.1.add_mem hy hIb
  exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [Y.2.1, (lagAct W n Y).2.1])).symm

end GlobalTheory.RallisCuspStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

variable {D : D7}

open Classical in

def restrictHalf {m n : ℕ} (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a' • x) * halfInd b Λ (b • x) * (if IsHalf (a' + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

open Classical in
theorem restrictHalf_apply {m n : ℕ} (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (x : Mx D m n) :
    restrictHalf a' b Λ Φ x = Φ (a' • x) * halfInd b Λ (b • x) * (if IsHalf (a' + b) x then 1 else 0) := rfl

end GlobalTheory.ExportSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorFamilyProdUpdate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

theorem prod_toList_insert_comm {ι M : Type} [Monoid M] [DecidableEq ι] (s : Finset ι) (v : ι) (hv : v ∉ s) (f : ι → M)
    (hc : ∀ a b, a ≠ b → Commute (f a) (f b)) :
    ((insert v s).toList.map f).prod = (s.toList.map f).prod * f v := by
  have hp : ((insert v s).toList.map f).Perm ((v :: s.toList).map f) := (Finset.toList_insert hv).map f
  have hpw : ((insert v s).toList.map f).Pairwise Commute := by
    rw [List.pairwise_map]
    exact (Finset.nodup_toList _).imp fun h => hc _ _ h
  rw [hp.prod_eq' hpw, List.map_cons, List.prod_cons]
  refine (Commute.list_prod_right _ _ fun y hy => ?_).eq
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
  refine hc _ _ ?_
  rintro rfl
  exact hv (Finset.mem_toList.1 hw)

theorem fid_orth (D : D7) {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) : fid D v * fid D w = 0 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  unfold fid
  split_ifs with h1 h2
  · obtain ⟨ε, hε, e⟩ := h1.choose_spec
    obtain ⟨ε', hε', e'⟩ := h2.choose_spec
    rw [e, e']
    exact GlobalTheory.IdemSupport.place_orth hΦ hε hε' h
  · exact mul_zero _
  · exact zero_mul _
  · exact zero_mul _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rep_mem_locSet {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    rep x ∈ locSet R i v := (Quotient.out x).2

theorem rep_commute {R : RealDat D A Ks} {i : Fin D.R.m} {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w)
    (x : LX R i v) (y : LX R i w) : Commute (rep x) (rep y) :=
  GlobalTheory.IdemSupport.commute_of_suppF _ (fid_orth D h) (rep_mem_locSet x).2 (rep_mem_locSet y).2

theorem famProd_mem_GfC (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) :
    famProd R i F ∈ GfC (Wc D i) := by
  unfold famProd
  split_ifs with h
  · refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
    exact (rep_mem_locSet _).1
  · exact Subgroup.one_mem _

theorem bop_congr (R : RealDat D A Ks) (i : Fin D.R.m) {γ γ' : GA D (Wc D i)}
    (h : trPair R i γ = trPair R i γ') : Bop R i γ = Bop R i γ' := by
  unfold Bop
  rw [h]

theorem famProd_update_of_ne (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v)
    (hF : {w | F w ≠ lx0 R i w}.Finite) (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : F v = lx0 R i v) (x : LX R i v)
    (hx : x ≠ lx0 R i v) : famProd R i (Function.update F v x) = famProd R i F * rep x := by
  have hs : {w | Function.update F v x w ≠ lx0 R i w} = insert v {w | F w ≠ lx0 R i w} := by
    ext w
    by_cases hw : w = v
    · subst hw
      simp [hx]
    · simp [hw]
  have hF' : {w | Function.update F v x w ≠ lx0 R i w}.Finite := by
    rw [hs]; exact hF.insert v
  have ht : hF'.toFinset = insert v hF.toFinset := by
    ext w
    rw [Set.Finite.mem_toFinset, hs, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_insert_iff]
  have hnv : v ∉ hF.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact fun h => h hv
  unfold famProd
  rw [dif_pos hF, dif_pos hF', ht,
    prod_toList_insert_comm hF.toFinset v hnv (fun w => rep (Function.update F v x w))
      (fun a b h => rep_commute h _ _)]
  congr 1
  · congr 1
    refine List.map_congr_left fun w hw => ?_
    have : w ≠ v := by
      rintro rfl
      exact hnv (Finset.mem_toList.1 hw)
    rw [Function.update_of_ne this]
  · simp only [Function.update_self]

theorem bop_famProd_update : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i, TransLaws R i → ∀ (F : ∀ v, Eu.LX R i v), {w | F w ≠ Eu.lx0 R i w}.Finite → ∀ v, F v = Eu.lx0 R i v → Eu.famProd R i F ∈ GfC (Wc D i) ∧ ∀ x : Eu.LX R i v, Eu.Bop R i (Eu.famProd R i (Function.update F v x)) = Eu.Bop R i (Eu.famProd R i F * Eu.rep x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hTL F hF v hv
  refine ⟨famProd_mem_GfC R i F, fun x => ?_⟩
  by_cases hx : x = lx0 R i v
  · have hu : Function.update F v x = F := by
      rw [hx, ← hv]; exact Function.update_eq_self v F
    rw [hu]
    refine bop_congr R i (funext fun a => funext fun b => ?_)
    have := hTL.2.2.2.1 _ (famProd_mem_GfC R i F) 1 (Subgroup.one_mem _) (rep x) (hx ▸ trivial_level_coset_representative_mem_level R i v) a b
    rw [one_mul] at this
    exact this.symm
  · rw [famProd_update_of_ne R i F hF v hv x hx]

end GlobalTheory.RawLift.Eu

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLatticeIndexSumLeZetaSqSubOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_lattice_index_sum_le_zeta_sq_sub_one : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ (∏ i ∈ Finset.range W.rank, (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1 := by
  first | exact @GlobalTheory.SplitIndexSum.indexSum_split | exact GlobalTheory.SplitIndexSum.indexSum_split | (intros; apply GlobalTheory.SplitIndexSum.indexSum_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGoodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameTwistFamily_specialization_good : ∀ (D : D7) (C A : Type) [AddCommGroup C] [CommGroup A] (u : UnivTwist D C) (Q : Finset (Pl D.host.E)) (χ : Multiplicative (↥Q → C) →* A), u.Good Q → (u.spec Q χ).Good := by
  first | exact @GlobalTheory.ExportSeries.SpecGood.spec_good | exact GlobalTheory.ExportSeries.SpecGood.spec_good | (intros; apply GlobalTheory.ExportSeries.SpecGood.spec_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceBaseChangeFieldStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_base_change_field : ∀ (E L E' L' : Type) [Field E] [Field L] [Algebra E L] [FiniteDimensional E L] [Field E'] [Field L'] [Algebra E' L'] (j : E →+* E') (jL : L →+* L'), (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Module.finrank E' L' = Module.finrank E L → ∀ z, Algebra.trace E' L' (jL z) = j (Algebra.trace E L z) := by
  first | exact @GlobalTheory.trace_map_of_adjoin_range_eq_top_of_finrank_eq | exact GlobalTheory.trace_map_of_adjoin_range_eq_top_of_finrank_eq | (intros; apply GlobalTheory.trace_map_of_adjoin_range_eq_top_of_finrank_eq <;> assumption)
end

