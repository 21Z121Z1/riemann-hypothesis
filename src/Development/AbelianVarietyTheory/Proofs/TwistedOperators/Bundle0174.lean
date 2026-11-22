import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0139
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvTransposeInvTranspose
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix
open scoped TensorProduct

namespace GlobalTheory.LocalThetaGL

section Abstract

variable {H V W U Y Γ : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Y] [Module ℂ Y] {P : Subgroup H}

def onRight (V : Type) [AddCommGroup V] [Module ℂ V] {G : Type} [Group G] (σ : Representation ℂ G W) :
    Representation ℂ G (V ⊗[ℂ] W) where
  toFun g := (σ g).lTensor V
  map_one' := by simp only [map_one]; exact LinearMap.lTensor_id _ _
  map_mul' g h := by simp only [map_mul]; exact LinearMap.lTensor_comp _ _ _

theorem isSmooth_onRight {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) : IsSmooth (onRight V σ) := by
  intro x
  show x ∈ smoothPart (onRight V σ)
  induction x with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul v w =>
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((hσ w).mem_nhds (by simp)) fun g hg => ?_)
    have h2 : σ g w = w := hg
    show (σ g).lTensor V (v ⊗ₜ w) = _
    rw [LinearMap.lTensor_tmul, h2]

def tmulMap {G : Type} [Group G] (σ : Representation ℂ G W) (v : V) : σ.IntertwiningMap (onRight V σ) where
  toLinearMap := TensorProduct.mk ℂ V W v
  isIntertwining' _ := rfl

def tensorInd (σ : Representation ℂ P W) :
    V ⊗[ℂ] smoothPart (ind P σ) →ₗ[ℂ] smoothPart (ind P (onRight V σ)) :=
  TensorProduct.lift
    { toFun := fun v => (smIndMap (tmulMap σ v)).toLinearMap
      map_add' := fun v v' => LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x =>
        TensorProduct.add_tmul v v' (f.1.1 x)))
      map_smul' := fun c v => LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x =>
        (TensorProduct.smul_tmul' c v (f.1.1 x)).symm)) }

theorem tensorInd_apply (σ : Representation ℂ P W) (t : V ⊗[ℂ] smoothPart (ind P σ)) (x : H) :
    (tensorInd σ t).1.1 x = (MultiIrr.ev σ x).lTensor V t := by
  induction t with
  | zero => simp
  | add s t hs ht => simp only [map_add, ← hs, ← ht]; rfl
  | tmul v f => rfl

theorem tensorInd_bijective (σ : Representation ℂ P W) {K : Set H} (hK : IsCompact K)
    (hPK : ∀ x, ∃ p : P, ∃ w ∈ K, x = p * w) : Function.Bijective (tensorInd (V := V) σ) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => MultiIrr.eq_zero_of_ev σ t fun x => ?_, fun f => ?_⟩
  · rw [← tensorInd_apply, ht]; rfl
  · obtain ⟨t, ht⟩ := MultiIrr.exists_tensor σ hK hPK f.1.1 f.1.2 (MultiIrr.eventually_of_smooth f)
    exact ⟨t, Subtype.ext (Subtype.ext (funext fun x => (tensorInd_apply σ t x).trans (ht x)))⟩

theorem exists_factor (f : V →ₗ[ℂ] W) (g : V →ₗ[ℂ] U) (hf : Function.Surjective f)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : ∃ T : W →ₗ[ℂ] U, ∀ v, T (f v) = g v := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  refine ⟨g ∘ₗ s, fun v => ?_⟩
  have : s (f v) - v ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact LinearMap.congr_fun hs (f v)
  have := h this
  rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this

def contract (L : Submodule ℂ (Module.Dual ℂ V)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] :
    V →ₗ[ℂ] L ⊗[ℂ] Y →ₗ[ℂ] Y :=
  ((dualTensorHom ℂ V Y) ∘ₗ L.subtype.rTensor Y).flip

theorem exists_lift [T2Space H] {K : Subgroup H} (hP : IsClosed (P : Set H)) (hK : IsCompact (K : Set H))
    (hPK : ∀ g : H, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hb : ∀ U ∈ nhds (1 : H), ∃ J : Subgroup H, IsOpen (J : Set H) ∧ (J : Set H) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    {σ : Representation ℂ P W} (hσ : IsSmooth σ) {ρ : Representation ℂ P U}
    (R : Γ → V →ₗ[ℂ] V) (S : Γ → σ.IntertwiningMap σ) (A : V →ₗ[ℂ] σ.IntertwiningMap ρ)
    (hs : ∀ u, ∃ v w, A v w = u)
    (hu : ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (B : W →ₗ[ℂ] V →ₗ[ℂ] Z),
      (∀ γ w v, B (S γ w) (R γ v) = B w v) → ∃ B₀ : U →ₗ[ℂ] Z, ∀ w v, B w v = B₀ (A v w))
    {π' : Representation ℂ H Y} (B : V →ₗ[ℂ] (smInd P σ).IntertwiningMap π')
    (hB : ∀ γ v f, B (R γ v) (smIndMap (S γ) f) = B v f) :
    ∃ T : (smInd P ρ).IntertwiningMap π', ∀ v f, T (smIndMap (A v) f) = B v f := by
  let α : (onRight V σ).IntertwiningMap ρ :=
    { toLinearMap := TensorProduct.lift
        { toFun := fun v => (A v).toLinearMap
          map_add' := fun v v' => by rw [map_add]; rfl
          map_smul' := fun c v => by rw [map_smul]; rfl }
      isIntertwining' := fun p => TensorProduct.ext' fun v w => (A v).isIntertwining _ _ p w }
  have hα : ∀ v w, α (v ⊗ₜ w) = A v w := fun _ _ => rfl
  let T : Γ → (onRight V σ).IntertwiningMap (onRight V σ) := fun γ =>
    { toLinearMap := TensorProduct.map (R γ) (S γ).toLinearMap
      isIntertwining' := fun p => TensorProduct.ext' fun v w =>
        congrArg (fun z => R γ v ⊗ₜ[ℂ] z) ((S γ).isIntertwining _ _ p w) }
  obtain ⟨h1, h2⟩ := GlobalTheory.SmGL.IndCoinv.smInd_coinvariants H P K hP hK hPK hb _ U (onRight V σ) ρ (isSmooth_onRight hσ) α Γ T
    (fun u => by obtain ⟨v, w, rfl⟩ := hs u; exact ⟨v ⊗ₜ w, rfl⟩) (fun x hx => by
      set N := Submodule.span ℂ {y : V ⊗[ℂ] W | ∃ γ z, y = T γ z - z}
      obtain ⟨B₀, hB₀⟩ := hu _ ((TensorProduct.mk ℂ V W).flip.compr₂ N.mkQ) fun γ w v =>
        (Submodule.Quotient.eq N).2 (Submodule.subset_span ⟨γ, v ⊗ₜ w, rfl⟩)
      have : N.mkQ = B₀ ∘ₗ α.toLinearMap := TensorProduct.ext' fun v w => hB₀ w v
      have h0 : N.mkQ x = 0 := by
        rw [this]
        show B₀ (α x) = 0
        rw [hx, map_zero]
      exact (Submodule.Quotient.mk_eq_zero N).1 h0)
  let E := LinearEquiv.ofBijective _ (tensorInd_bijective (V := V) σ hK fun x => by
    obtain ⟨p, hp, w, hw, e⟩ := hPK x
    exact ⟨⟨p, hp⟩, w, hw, e⟩)
  let β : V ⊗[ℂ] smoothPart (ind P σ) →ₗ[ℂ] Y := TensorProduct.lift
    { toFun := fun v => (B v).toLinearMap
      map_add' := fun v v' => by rw [map_add]; rfl
      map_smul' := fun c v => by rw [map_smul]; rfl }
  have hker : LinearMap.ker (smIndMap α).toLinearMap ≤ LinearMap.ker (β ∘ₗ E.symm.toLinearMap) := by
    intro f hf
    refine Submodule.span_le.2 ?_ (h2 f hf)
    rintro _ ⟨γ, z, rfl⟩
    obtain ⟨t, rfl⟩ := E.surjective z
    have e1 : smIndMap (T γ) (E t) = E (TensorProduct.map (R γ) (smIndMap (S γ)).toLinearMap t) := by
      induction t with
      | zero => simp
      | add s t hs ht => simp only [map_add, hs, ht]
      | tmul v f => rfl
    have e2 : β (TensorProduct.map (R γ) (smIndMap (S γ)).toLinearMap t) = β t :=
      LinearMap.congr_fun (f := β ∘ₗ TensorProduct.map (R γ) (smIndMap (S γ)).toLinearMap) (g := β)
        (TensorProduct.ext' fun v f => hB γ v f) t
    show β (E.symm _) = 0
    rw [e1, map_sub, E.symm_apply_apply, E.symm_apply_apply, map_sub, e2, sub_self]
  obtain ⟨T₀, hT₁⟩ := exists_factor _ _ h1 hker
  have hT₀ : ∀ t, T₀ (smIndMap α (E t)) = β t := fun t =>
    (hT₁ (E t)).trans (congrArg β (E.symm_apply_apply t))
  have hT : ∀ v f, T₀ (smIndMap (A v) f) = B v f := fun v f => hT₀ (v ⊗ₜ f)
  refine ⟨⟨T₀, fun h => LinearMap.ext fun u => ?_⟩, hT⟩
  obtain ⟨z, rfl⟩ := h1 u
  obtain ⟨t, rfl⟩ := E.surjective z
  show T₀ (smInd P ρ h _) = π' h (T₀ _)
  induction t with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul v f => exact (hT v (smInd P σ h f)).trans (((B v).isIntertwining _ _ h f).trans (congrArg _ (hT v f).symm))

end Abstract

section Regular

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] {π : Representation ℂ G V}

def act (hπ : IsSmooth π) : V →ₗ[ℂ] SB G →ₗ[ℂ] V :=
  LinearMap.flip
    { toFun := fun φ => smoothOp π ν φ.1
      map_add' := fun φ ψ => hπ.smoothOp_add φ.2.1 φ.2.2 ψ.2.1 ψ.2.2
      map_smul' := fun c φ => hπ.smoothOp_smul φ.2.1 φ.2.2 c }

end Regular

section Local

open GlobalTheory.IndefiniteRowSideFullHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

theorem compact_open_basis (n : Type) [Fintype n] [DecidableEq n] : ∀ U ∈ nhds (1 : GL n k),
    ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ IsCompact (K : Set (GL n k)) ∧ (K : Set (GL n k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k n U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end Local

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

def contraMap [TopologicalSpace G] [IsTopologicalGroup G] {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : π.IntertwiningMap σ) : (contra σ).IntertwiningMap (contra π) where
  toLinearMap := (f.toLinearMap.dualMap ∘ₗ Submodule.subtype _).codRestrict _ fun l =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds l.2 (by
      rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply])) fun g hg =>
      LinearMap.ext fun v => by
        have h1 : l.1 (σ g⁻¹ (f v)) = l.1 (f v) := LinearMap.congr_fun hg (f v)
        show l.1 (f (π g⁻¹ v)) = l.1 (f v)
        rw [f.isIntertwining, h1])
  isIntertwining' g := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun v => by
    show l.1 (σ g⁻¹ (f v)) = l.1 (f (π g⁻¹ v))
    rw [f.isIntertwining])

theorem isUnitarisable_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ)
    (h : IsUnitarisable σ) : IsUnitarisable π := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B.comp E.toLinearMap).compl₂ E.toLinearMap, fun v w => h1 _ _, fun v hv => h2 _ ?_, fun g v w => ?_⟩
  · exact fun h => hv (E.toLinearEquiv.map_eq_zero_iff.1 h)
  · show B (E.toIntertwiningMap (π g v)) (E.toIntertwiningMap (π g w)) = _
    rw [E.toIntertwiningMap.isIntertwining, E.toIntertwiningMap.isIntertwining, h3]
    rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Main

section Final

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

theorem isIrreducible_twist {π : Representation ℂ G V} (h : π.IsIrreducible) (χ : G →* ℂˣ) :
    (twist π χ).IsIrreducible := by
  let φ : Subrepresentation (twist π χ) ≃o Subrepresentation π :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem ((χ g)⁻¹ : ℂˣ) (S.apply_mem_toSubmodule g hv)
        rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact φ.isSimpleOrder_iff.2 h

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invTranspose_invTranspose {n : ℕ} (g : GL (Fin n) k) :
    WeilTensorLiftConclusion.invTranspose n k (WeilTensorLiftConclusion.invTranspose n k g) = g := Units.ext (transpose_transpose _)

end Final

end GlobalTheory.LocalThetaGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDefiniteSelfDualOfBaseFramePosDef
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameUnimod

theorem isLattice_of_squeeze {E M : Type} [Field E] [NumberField E] [AddCommGroup M] [Module E M] [Module (𝓞 E) M]
    [IsScalarTower (𝓞 E) E M] {L Λ : Submodule (𝓞 E) M} (hL : Submodule.IsLattice E L) {c : E} (hc : c ≠ 0)
    (h1 : ∀ x ∈ L, c • x ∈ Λ) (h2 : ∀ x ∈ Λ, c • x ∈ L) : Submodule.IsLattice E Λ := by
  let f : M →ₗ[𝓞 E] M := ((c⁻¹ • LinearMap.id : M →ₗ[E] M)).restrictScalars (𝓞 E)
  constructor
  · have hfg : (L.map f).FG := hL.fg.map f
    have hle : Λ ≤ L.map f := fun x hx => ⟨c • x, h2 x hx, by simp [f, smul_smul, hc]⟩
    exact hfg.of_le hle
  · rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have : x = c⁻¹ • (c • x) := by simp [smul_smul, hc]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (h1 x hx))

theorem coe_span_dualSet {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) :
    (Submodule.span (𝓞 E) (dualSet σ J L) : Set (n → E)) = dualSet σ J L := by
  refine Set.Subset.antisymm (fun y hy => ?_) Submodule.subset_span
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => intro x _; simpa [Formalism.UG.hform] using (algebraMap (𝓞 E) E).range.zero_mem
  | add y z _ _ hy hz =>
    intro x hx
    have : Formalism.UG.hform σ J x (y + z) = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x z := by
      simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
    rw [this]
    exact add_mem (hy x hx) (hz x hx)
  | smul a y _ hy =>
    intro x hx
    have : Formalism.UG.hform σ J x (a • y) = algebraMap (𝓞 E) E a * Formalism.UG.hform σ J x y := by
      simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact mul_mem ⟨a, rfl⟩ (hy x hx)

theorem isDefUnimod_of_isBaseFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), V.SigOK → V.IsPosDef → IsBaseFrame V β Λ N → IsDefUnimod D.sp.cm V.gram Λ := by
  intro D V β Λ N hs hp ⟨_, hdual, hN, h1, h2⟩
  obtain ⟨-, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hL : Submodule.IsLattice D.host.E (Formalism.L2.Herm.crdLat V V.L0) :=
    Formalism.MainNotions.StandardLattice.tMap_lattice (Formalism.L2.Herm.crd V) V.L0 V.standardTuple_isLattice
  have hmem : ∀ x, x ∈ Formalism.L2.Herm.crdLat V V.L0 ↔ x ∈ L0c D V := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  refine ⟨Matrix.ext fun i j => (hJ V).1 i j, (hJ V).2.isUnit,
    GlobalTheory.Proof.TotallyDefiniteMass.isTotDef_gram D.sp.cm V hs hp,
    isLattice_of_squeeze hL (Nat.cast_ne_zero.2 hN.ne') (fun x hx => h1 x ((hmem x).1 hx))
      (fun x hx => (hmem _).2 (h2 x hx)), ?_⟩
  rw [← coe_span_dualSet]
  exact congrArg SetLike.coe hdual

end GlobalTheory.BaseFrameUnimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
section
noncomputable section

namespace GlobalTheory.CoinvKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def IsStabW (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  N ≤ A ∧ (∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N) ∧
    (∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N) ∧
    ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def HasRelY (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  (∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ A, om (g, 1) Φ - Φ ∈ N) ∧
    (∀ k ∈ KInf σ Y emb, ∀ Φ ∈ A, om (k, 1) Φ - Φ ∈ N) ∧
    ∀ γ ∈ Lines σ Y, ∀ Φ ∈ A, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def IsThetaSub (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  IsStabW om emb A N ∧ HasRelY om emb A N

end GlobalTheory.CoinvKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaStdMaxParab
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.MaxParabIwasawa

theorem iwasawa_stdMaxParab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r a b : ℕ) (h : a + b = r) (g : GL (Fin r) k),
    (∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, g = κ * p) ∧
      ∃ p ∈ stdMaxParab k h, ∃ κ ∈ KO k (Fin r), g = p * κ := by
  intro k _ _ _ _ r a b h g
  have key : ∀ x : GL (Fin r) k, ∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, x = κ * p := by
    intro x
    obtain ⟨k₀, p, hp, hx⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r x
    have hpP : p ∈ stdMaxParab k h := (mem_stdMaxParab h).2 fun i j hj hi =>
      hp (show j < i from by rw [Fin.lt_def]; omega)
    exact ⟨_, ⟨k₀, rfl⟩, p, hpP, hx⟩
  refine ⟨key g, ?_⟩
  obtain ⟨κ, hκ, p, hp, e⟩ := key g⁻¹
  refine ⟨p⁻¹, inv_mem hp, κ⁻¹, inv_mem hκ, ?_⟩
  rw [← mul_inv_rev, ← e, inv_inv]

end GlobalTheory.MaxParabIwasawa

example : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r a b : ℕ)
    (h : a + b = r) (g : GL (Fin r) k), (∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, g = κ * p) ∧
    ∃ p ∈ stdMaxParab k h, ∃ κ ∈ KO k (Fin r), g = p * κ := GlobalTheory.MaxParabIwasawa.iwasawa_stdMaxParab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteApproximateIdentity
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

noncomputable section
namespace GlobalTheory.KFinReproduce

variable {n : ℕ} {ε : Fin n → Bool}

def kfinFuns (ε : Fin n → Bool) : Submodule ℂ (KG ε → ℂ) where
  carrier := {e | KFinFun ε e}
  add_mem' := by
    rintro a b ⟨F, hF, ha, hc, ht⟩ ⟨F', hF', hb, hc', ht'⟩
    refine ⟨F ⊔ F', inferInstance, Submodule.add_mem_sup ha hb, fun φ hφ => ?_, fun φ hφ k₀ => ?_⟩
    · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hφ
      exact (hc u hu).add (hc' v hv)
    · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hφ
      exact ⟨Submodule.add_mem_sup (ht u hu k₀).1 (ht' v hv k₀).1,
        Submodule.add_mem_sup (ht u hu k₀).2 (ht' v hv k₀).2⟩
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun φ hφ => by
      rw [(Submodule.mem_bot _).1 hφ]; exact continuous_const,
    fun φ hφ k₀ => by
      rw [(Submodule.mem_bot _).1 hφ]; exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩⟩
  smul_mem' := by
    rintro c a ⟨F, hF, ha, hc, ht⟩
    exact ⟨F, hF, F.smul_mem c ha, hc, ht⟩

theorem continuous_of_kFinFun {e : KG ε → ℂ} (h : KFinFun ε e) : Continuous e := by
  obtain ⟨F, -, he, hc, -⟩ := h
  exact hc e he

theorem integrable_mul {e F : KG ε → ℂ} (he : Continuous e) (hF : Continuous F) :
    Integrable (fun k => e k * F k) (muK ε) :=
  (he.mul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def intSpace {ι : Type} (F : ι → KG ε → ℂ) (hF : ∀ j, Continuous (F j)) : Submodule ℂ (ι → ℂ) where
  carrier := {v | ∃ e, KFinFun ε e ∧ ∀ j, ∫ k, e k * F j k ∂(muK ε) = v j}
  add_mem' := by
    rintro a b ⟨e, he, hea⟩ ⟨e', he', heb⟩
    refine ⟨e + e', (kfinFuns ε).add_mem he he', fun j => ?_⟩
    simp only [Pi.add_apply, add_mul]
    rw [MeasureTheory.integral_add (integrable_mul (continuous_of_kFinFun he) (hF j)) (integrable_mul (continuous_of_kFinFun he') (hF j)), hea, heb]
  zero_mem' := ⟨0, (kfinFuns ε).zero_mem, fun j => by simp⟩
  smul_mem' := by
    rintro c a ⟨e, he, hea⟩
    refine ⟨c • e, (kfinFuns ε).smul_mem c he, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, hea]

end GlobalTheory.KFinReproduce

namespace GlobalTheory.KFinReproduce

end GlobalTheory.KFinReproduce
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlacesStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacters_ramification_levelPlaces : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Q t, (L.C.mu0 j).UnrAt PP) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ ∀ PP', PP' ∉ L.Pg → (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → (L.C.mu0 j).UnrAt PP' := by
  first | exact @GlobalTheory.LevelRamif.ramif_at_levels | exact GlobalTheory.LevelRamif.ramif_at_levels | (intros; apply GlobalTheory.LevelRamif.ramif_at_levels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlacesStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacters_unramified_off_levelPlaces : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ t : T0, Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ (∀ PP ∈ L.Q t, ∀ j, (L.C.mu0 j).UnrAt PP) ∧ ∀ P : Pl D.host.E, (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → PP.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F)) → (L.xiH t).UnrAt P ∧ ∀ j, (L.C.mu0 j).UnrAt P := by
  first | exact @GlobalTheory.levCh_unramified_places | exact GlobalTheory.levCh_unramified_places | (intros; apply GlobalTheory.levCh_unramified_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumValueEqProdLocalResidueValuesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatumValue_eq_prod_localResidueValues : ∀ (D : D7) (a b : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (χ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Hl : ∀ PP : ↥L.Pg, Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP.1))) (cl : ∀ PP : ↥L.Pg, Hl PP →* ℂˣ),
    L.P = Formalism.L2.DIV.LevelP.ofLocal Hl cl →
    ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP),
      omegaG L χ y = ∏ PP : ↥L.Pg, gLoc L PP.1 (Hl PP) (cl PP) (χ PP.1) (y PP.1) := by
  first | exact @GlobalTheory.StepVec.omegaG_eq_prod_gLoc | exact GlobalTheory.StepVec.omegaG_eq_prod_gLoc | (intros; apply GlobalTheory.StepVec.omegaG_eq_prod_gLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMemStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  first | exact @GlobalTheory.StabLatInv.mem_latO_iff_actO_mem | exact GlobalTheory.StabLatInv.mem_latO_iff_actO_mem | (intros; apply GlobalTheory.StabLatInv.mem_latO_iff_actO_mem <;> assumption)
end

