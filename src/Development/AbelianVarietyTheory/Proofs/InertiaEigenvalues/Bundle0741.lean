import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLevelDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LevelTypeProj

theorem span_eval_eq_top {X M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (ev : X → Module.Dual ℂ M) (hev : ∀ v, (∀ x, ev x v = 0) → v = 0) :
    Submodule.span ℂ (Set.range ev) = ⊤ := by
  have hbot : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact (Submodule.mem_bot ℂ).2 (hev v fun x => hv (ev x) (Submodule.subset_span ⟨x, rfl⟩))
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hbot,
    Submodule.dualAnnihilator_bot]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem finRep_cptRep (l : GL (Fin N) (Af E)) (k : Kinf E N) (φ : Sm E N) :
    finRep E N l (cptRep E N k φ) = cptRep E N k (finRep E N l φ) := by
  simp only [finRep, cptRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, ← infGL_comm, map_mul, Module.End.mul_apply]

def orbitSpan (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : Submodule ℂ (Sm E N) :=
  Submodule.span ℂ {v | ∃ l ∈ L, ∃ k, v = finRep E N l (cptRep E N k ψ)}

theorem mem_orbitSpan_self (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : ψ ∈ orbitSpan L ψ :=
  Submodule.subset_span ⟨1, L.one_mem, 1, by rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply]⟩

theorem orbitSpan_le {J : Submodule ℂ (Sm E N)} (hJ : IsStable J) (L : Subgroup (GL (Fin N) (Af E)))
    {ψ : Sm E N} (hψ : ψ ∈ J) : orbitSpan L ψ ≤ J :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, k, rfl⟩; exact hJ (.fin l) _ (hJ (.cpt k) _ hψ))

theorem finRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} {l' : GL (Fin N) (Af E)}
    (hl' : l' ∈ L) {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : finRep E N l' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l' * l, L.mul_mem hl' hl, k, ?_⟩
    rw [map_mul (finRep E N), Module.End.mul_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem cptRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} (k' : Kinf E N)
    {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : cptRep E N k' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l, hl, k' * k, ?_⟩
    rw [map_mul (cptRep E N), Module.End.mul_apply, finRep_cptRep l k' (cptRep E N k ψ)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem orbitSpan_finiteDimensional (L : Subgroup (GL (Fin N) (Af E))) (hL : IsCompact (L : Set (GL (Fin N) (Af E))))
    (ψ : Sm E N) (hψ : IsAutForm ψ) : FiniteDimensional ℂ (orbitSpan L ψ) := by
  classical
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun l : GL (Fin N) (Af E) => {m | finRep E N (l⁻¹ * m) ψ = ψ})
    (fun l => hψ.level.preimage (continuous_mul_left l⁻¹))
    (fun m _ => Set.mem_iUnion.2 ⟨m, by simp only [Set.mem_setOf_eq, inv_mul_cancel, map_one]; rfl⟩)
  have := hψ.kfin
  refine Submodule.finiteDimensional_of_le
    (S₂ := t.sup fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨m, hm, k, rfl⟩
  obtain ⟨l, hl, hlm⟩ := Set.mem_iUnion₂.1 (ht hm)
  have e : finRep E N m ψ = finRep E N l ψ := by
    calc finRep E N m ψ = finRep E N l (finRep E N (l⁻¹ * m) ψ) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = finRep E N l ψ := by rw [show finRep E N (l⁻¹ * m) ψ = ψ from hlm]
  refine Finset.le_sup (f := fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l)) hl ?_
  refine ⟨cptRep E N k ψ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  change finRep E N l (cptRep E N k ψ) = finRep E N m (cptRep E N k ψ)
  rw [finRep_cptRep, finRep_cptRep, e]

def typePart (L : Subgroup (GL (Fin N) (Af E))) {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Kinf E N) U) : Submodule ℂ (Sm E N) where
  carrier := {φ | (∀ k ∈ L, finRep E N k φ = φ) ∧
    ∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k hk => by rw [map_add, hx.1 k hk, hy.1 k hk],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ => map_zero _, fun _ => by
    simp only [map_zero, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k hk => by rw [map_smul, hx.1 k hk],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem exists_proj {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    (S : Submodule ℂ (Sm E N)) (hSW : S ≤ W) [FiniteDimensional ℂ S] :
    ∃ p : W →ₗ[ℂ] W, (∀ x, (p x).1 ∈ S) ∧
      ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0 := by
  haveI : FiniteDimensional ℂ (S.comap W.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hSW).symm.finiteDimensional
  let e := Submodule.equivMapOfInjective (toL2ₗ μ W h) hF (S.comap W.subtype)
  haveI : FiniteDimensional ℂ ((S.comap W.subtype).map (toL2ₗ μ W h)) := e.finiteDimensional
  have e1 : ∀ z, toL2ₗ μ W h ((e.symm z : S.comap W.subtype) : W) = (z : L2 (latticeGL E N) μ) := fun z => by
    have := Submodule.coe_equivMapOfInjective_apply (toL2ₗ μ W h) hF (S.comap W.subtype) (e.symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨(S.comap W.subtype).subtype ∘ₗ e.symm.toLinearMap ∘ₗ
    ((S.comap W.subtype).map (toL2ₗ μ W h)).orthogonalProjectionOnto.toLinearMap ∘ₗ toL2ₗ μ W h,
    fun x => (e.symm _).2, fun x y hy => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
  rw [e1]
  exact Submodule.starProjection_inner_eq_zero _ _ ⟨y, hy, rfl⟩

theorem proj_unique {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} {x a b : W} (ha : a.1 ∈ S) (hb : b.1 ∈ S)
    (hxa : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h a) (toL2ₗ μ W h y) = 0)
    (hxb : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h b) (toL2ₗ μ W h y) = 0) : a = b := by
  have hm : (b - a).1 ∈ S := S.sub_mem hb ha
  have key : toL2ₗ μ W h (b - a) = (toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b) := by
    rw [map_sub]; abel
  have h0 : inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a)) = 0 := by
    calc inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a))
        = inner ℂ ((toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b)) (toL2ₗ μ W h (b - a)) := by
          rw [← key]
      _ = 0 := by rw [inner_sub_left, hxa _ hm, hxb _ hm, sub_zero]
  exact (sub_eq_zero.1 (hF ((inner_self_eq_zero.1 h0).trans (map_zero _).symm))).symm

theorem proj_rt {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} (hSW : S ≤ W) (p : W →ₗ[ℂ] W) (hpS : ∀ x, (p x).1 ∈ S)
    (hp : ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0)
    (g : GA E N) (hgW : ∀ x ∈ W, rt E N g x ∈ W) (hgS : ∀ x ∈ S, rt E N g x ∈ S)
    (hgS' : ∀ x ∈ S, rt E N g⁻¹ x ∈ S) (x : W) :
    p ⟨rt E N g x.1, hgW _ x.2⟩ = ⟨rt E N g (p x).1, hgW _ (p x).2⟩ := by
  refine proj_unique h hF (hpS _) (hgS _ (hpS x)) (hp _) fun y hy => ?_
  have hy' : rt E N g⁻¹ y.1 ∈ W := hSW (hgS' _ hy)
  have ey : y = ⟨rt E N g (rt E N g⁻¹ y.1), hgW _ hy'⟩ := Subtype.ext (by
    show y.1 = rt E N g (rt E N g⁻¹ y.1)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
  rw [ey, ← R_toL2ₗ h x (hgW _ x.2), ← R_toL2ₗ h (p x) (hgW _ (p x).2), ← R_toL2ₗ h ⟨_, hy'⟩ (hgW _ hy'),
    ← map_sub]
  let Ui : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ := ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  change inner ℂ (Ui _) (Ui _) = 0
  rw [Ui.inner_map_map]
  exact hp x ⟨_, hy'⟩ (hgS' _ hy)

theorem exists_levelType_part : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W J : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1), IsStable W → (∀ φ ∈ W, IsAutForm φ) → IsStable J → J ≤ W → ∀ (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) → IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (ρ : Representation ℂ (Kinf E N) U), AutFin.IsContRep ρ → ∀ ψ : W, ψ.1 ∈ J → ∃ ψ' : W, ψ'.1 ∈ J ∧ (∀ k ∈ L, finRep E N k ψ'.1 = ψ'.1) ∧ (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k ψ'.1).1 g) ∈ AutFin.coeffSpan ρ) ∧ ∀ φ : W, (∀ k ∈ L, finRep E N k φ.1 = φ.1) → (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ.1).1 g) ∈ AutFin.coeffSpan ρ) → inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ) = inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ') := by
  intro E _ _ _ N μ _ _ W J h hW hA hJ hJW L _ hLc U _ _ _ ρ _ ψ hψ
  have hF := toL2ₗ_injective h fun φ hφ => ContAut.continuous_of_isOpen_stab E N φ (hA φ hφ).level
  have hSJ : orbitSpan L ψ.1 ≤ J := orbitSpan_le hJ L hψ
  have hSW := hSJ.trans hJW
  haveI := orbitSpan_finiteDimensional L hLc ψ.1 (hA _ ψ.2)
  haveI : FiniteDimensional ℂ (orbitSpan L ψ.1 ⊓ typePart L ρ : Submodule ℂ (Sm E N)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨p, hpS, hp⟩ := exists_proj h hF (orbitSpan L ψ.1) hSW
  obtain ⟨q, hqQ, hq⟩ := exists_proj h hF (orbitSpan L ψ.1 ⊓ typePart L ρ) (inf_le_left.trans hSW)
  refine ⟨q ψ, hSJ (hqQ ψ).1, (hqQ ψ).2.1, (hqQ ψ).2.2, fun φ hφL hφK => ?_⟩
  have hpT : (p φ).1 ∈ typePart L ρ := by
    refine ⟨fun k hk => ?_, fun g => ?_⟩
    · have hc := proj_rt h hF hSW p hpS hp (finGL E N k) (fun x hx => hW (.fin k) x hx)
        (fun x hx => finRep_mem_orbitSpan hk hx)
        (fun x hx => by rw [← map_inv]; exact finRep_mem_orbitSpan (L.inv_mem hk) hx) φ
      exact (congrArg Subtype.val hc).symm.trans (congrArg (fun x => (p x).1) (Subtype.ext (hφL k hk)))
    · have hcomm : ∀ k : Kinf E N, cptRep E N k (p φ).1 = (p ⟨cptRep E N k φ.1, hW (.cpt k) _ φ.2⟩).1 := fun k =>
        (congrArg Subtype.val (proj_rt h hF hSW p hpS hp (infGL E N (Unitary.toUnits k))
          (fun x hx => hW (.cpt k) x hx) (fun x hx => cptRep_mem_orbitSpan k hx)
          (fun x hx => by rw [← map_inv, ← map_inv]; exact cptRep_mem_orbitSpan k⁻¹ hx) φ)).symm
      have := (hA φ φ.2).kfin
      have hVW : Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1) ≤ W :=
        Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hW (.cpt k) _ φ.2)
      let V := Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1)
      let Λ : Module.Dual ℂ V →ₗ[ℂ] (Kinf E N → ℂ) :=
        { toFun := fun ℓ k => ℓ ⟨cptRep E N k φ.1, Submodule.subset_span ⟨k, rfl⟩⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let ev : GA E N → Module.Dual ℂ V := fun x => (LinearMap.proj x).comp ((Sm E N).subtype.comp V.subtype)
      have htop := span_eval_eq_top ev fun v hv => Subtype.ext (Subtype.ext (funext hv))
      have hle : Submodule.span ℂ (Set.range ev) ≤ (AutFin.coeffSpan ρ).comap Λ :=
        Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hφK x)
      let ℓ : Module.Dual ℂ V :=
        (LinearMap.proj g).comp ((Sm E N).subtype.comp (W.subtype.comp (p.comp (Submodule.inclusion hVW))))
      have hℓ : Λ ℓ ∈ AutFin.coeffSpan ρ := hle (htop ▸ Submodule.mem_top)
      convert hℓ using 1
      funext k
      rw [hcomm k]
      rfl
  have hψS : ψ.1 ∈ orbitSpan L ψ.1 := mem_orbitSpan_self L ψ.1
  have hr : (ψ - q ψ).1 ∈ orbitSpan L ψ.1 := (orbitSpan L ψ.1).sub_mem hψS (hqQ ψ).1
  have h1 : inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h (ψ - q ψ)) =
      inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) := by
    have := hp φ (ψ - q ψ) hr
    rwa [inner_sub_left, sub_eq_zero] at this
  have h2 : inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) = 0 := by
    have := hq ψ (p φ) ⟨hpS φ, hpT⟩
    rw [map_sub, ← inner_conj_symm, this, map_zero]
  rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, h1, h2]

end GlobalTheory.LevelTypeProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionHeisenbergIrreducibleOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.ThetaIrred

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem integrable_star_mul (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1)
    {f g q : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (hq : Continuous q)
    {Cq : ℝ} (hCq : ∀ x, ‖q x‖ ≤ Cq) :
    Integrable (fun x => star (f x) * (q x * g x)) (μ.restrict 𝓕) := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨Cf, hCf⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hf
  obtain ⟨Cg, hCg⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hg
  refine Integrable.of_bound (hf.cont.star.mul (hq.mul hg.cont)).aestronglyMeasurable (Cf * (Cq * Cg))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have a0 : 0 ≤ Cq := (norm_nonneg _).trans (hCq x)
  have b0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf x)
  exact mul_le_mul (hCf x) (mul_le_mul (hCq x) (hCg x) (norm_nonneg _) a0) (by positivity) b0

theorem orth_periodic (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1)
    {h k : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) (hk : IsThetaFunO ψ S T k)
    (horth : ∀ γ ∈ ratL T S, thetaIP μ 𝓕 h (heisO ψ S T γ k) = 0)
    {q : WO S T → ℂ} (hq : Continuous q) (hqp : ∀ γ ∈ ratL T S, ∀ x, q (γ + x) = q x)
    {Cq : ℝ} (hCq : ∀ x, ‖q x‖ ≤ Cq) :
    ∫ x in 𝓕, star (h x) * (q x * k x) ∂μ = 0 := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  obtain ⟨Ch, hCh⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hh
  obtain ⟨Ck, hCk⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hk
  have ch0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0)
  have ck0 : 0 ≤ Ck := (norm_nonneg _).trans (hCk 0)
  set I := ∫ x in 𝓕, star (h x) * (q x * k x) ∂μ with hIdef
  have hint := integrable_star_mul hψ h1 hh hk hq hCq
  have key : ∀ δ : ℝ, 0 < δ → ‖I‖ ≤ δ * (Ch * Ck) := by
    intro δ hδ
    obtain ⟨s, c, hsc⟩ := GlobalTheory.ThetaSchurBdd.trig_approx hψ hq hqp hδ
    have hpk := GlobalTheory.ThetaSchurBdd.trig_mul_eq s c hk
    have hsum : ∀ x, star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) =
        ∑ a ∈ s, c a * (star (h x) * heisO ψ S T a k x) := by
      intro x
      have := congrFun hpk x
      rw [this, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    have hint_a : ∀ a ∈ s, Integrable (fun x => c a * (star (h x) * heisO ψ S T a k x)) (μ.restrict 𝓕) := by
      intro a _
      have := integrable_star_mul hψ h1 hh (hth a k hk) (q := fun _ => (1 : ℂ)) continuous_const (Cq := 1)
        (fun _ => by simp)
      simp only [one_mul] at this
      exact this.const_mul (c a)
    have hP : ∫ x in 𝓕, star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) ∂μ = 0 := by
      simp_rw [hsum]
      rw [integral_finset_sum s hint_a]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [integral_const_mul]
      have := horth a a.2
      unfold thetaIP at this
      rw [this, mul_zero]
    have hPint : Integrable (fun x => star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)) (μ.restrict 𝓕) := by
      simp_rw [hsum]
      exact integrable_finset_sum s hint_a
    have hdiff : I = ∫ x in 𝓕, (star (h x) * (q x * k x) -
        star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)) ∂μ := by
      rw [integral_sub hint hPint, hP, sub_zero]
    rw [hdiff]
    have hb : ∀ᵐ x ∂(μ.restrict 𝓕), ‖star (h x) * (q x * k x) -
        star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)‖ ≤ δ * (Ch * Ck) := by
      refine Filter.Eventually.of_forall fun x => ?_
      rw [show star (h x) * (q x * k x) - star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) =
        star (h x) * ((q x - ∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) by ring]
      rw [norm_mul, norm_mul, norm_star]
      have e1 := hsc x
      calc ‖h x‖ * (‖q x - ∑ a ∈ s, c a * ψ (symplO S T x a)‖ * ‖k x‖) ≤ Ch * (δ * Ck) :=
            mul_le_mul (hCh x) (mul_le_mul e1 (hCk x) (norm_nonneg _) hδ.le) (by positivity) ch0
        _ = δ * (Ch * Ck) := by ring
    refine (norm_integral_le_of_norm_le_const hb).trans ?_
    rw [measureReal_def, Measure.restrict_apply_univ, h1, ENNReal.toReal_one, mul_one]
  by_contra hne
  have hpos : 0 < ‖I‖ := norm_pos_iff.2 hne
  have hM : 0 < Ch * Ck + 1 := by positivity
  have := key (‖I‖ / (Ch * Ck + 1)) (div_pos hpos hM)
  rw [div_mul_eq_mul_div, le_div_iff₀ hM] at this
  nlinarith

theorem pointwise (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕)
    {h k : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) (hk : IsThetaFunO ψ S T k)
    (horth : ∀ γ ∈ ratL T S, thetaIP μ 𝓕 h (heisO ψ S T γ k) = 0) (x : WO S T) :
    h x = 0 ∨ k x = 0 := by
  have h1 : μ 𝓕 = 1 := hcv.2.2
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨Ch, hCh⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hh
  obtain ⟨Ck, hCk⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hk
  have ch0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0)
  set q : WO S T → ℂ := fun x => h x * star (k x) with hq
  have hqc : Continuous q := hh.cont.mul hk.cont.star
  have hqb : ∀ x, ‖q x‖ ≤ Ch * Ck := fun x => by
    rw [hq, norm_mul, norm_star]
    exact mul_le_mul (hCh x) (hCk x) (norm_nonneg _) ch0
  have hqp : ∀ γ ∈ ratL T S, ∀ x, q (γ + x) = q x := fun γ hγ x =>
    GlobalTheory.ThetaSchur.prod_periodic hψ hh hk hγ x
  have hz := orth_periodic hψ h1 hh hk horth hqc hqp hqb
  set F : WO S T → ℝ := fun x => ‖h x‖ ^ 2 * ‖k x‖ ^ 2 with hF
  have hpt : ∀ x, star (h x) * (q x * k x) = ((F x : ℝ) : ℂ) := by
    intro x
    rw [hq, hF, show star (h x) * (h x * star (k x) * k x) = (star (h x) * h x) * (star (k x) * k x) by ring]
    simp only [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have hint := integrable_star_mul hψ h1 hh hk hqc hqb
  simp_rw [hpt] at hz hint
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hz
  have hFi : Integrable F (μ.restrict 𝓕) := by
    have := hint.re
    simpa using this
  have hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hFi).1 hz
  have hf := GlobalTheory.ThetaSchurBdd.isTheta_star_mul_mul hψ hk hk hh
  have h0 : nrm2 μ 𝓕 (fun x => star (k x) * k x * h x) = 0 := by
    unfold nrm2
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with y hy
    have e : ‖star (k y) * k y * h y‖ ^ 2 = ‖k y‖ ^ 2 * F y := by
      rw [hF, norm_mul, norm_mul, norm_star]; ring
    rw [Pi.zero_apply, e, hy, mul_zero]
  have := congrFun (GlobalTheory.ThetaSchurBdd.thetaFunction_eq_zero_of_meanSquare_zero hψ hcv hf h0) x
  simp only [Pi.zero_apply, mul_eq_zero, star_eq_zero, or_self] at this
  exact this.symm

end GlobalTheory.ThetaIrred

theorem GlobalTheory.ThetaIrred.orth_heis_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ w : WO S T, thetaIP μ 𝓕 h (heisO ψ S T w e) = 0) → h = 0 ∨ e = 0 := by
  intro D ψ S T hψ μ 𝓕 hcv h e hh he horth
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hhh := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1
  have key : ∀ w x, h x = 0 ∨ heisO ψ S T w e x = 0 := by
    intro w x
    refine GlobalTheory.ThetaIrred.pointwise hψ hcv hh (hth w e he) (fun γ _ => ?_) x
    rw [hhh γ w e]
    unfold thetaIP
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (star (h _))]
    rw [integral_const_mul]
    have := horth (γ + w)
    unfold thetaIP at this
    rw [this, mul_zero]
  by_cases he0 : e = 0
  · exact Or.inr he0
  left
  obtain ⟨y, hy⟩ : ∃ y, e y ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact he0 (funext hn)
  funext x
  rcases key (y - x) x with h0 | h0
  · exact h0
  · exfalso
    simp only [heisO, add_sub_cancel] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact GlobalTheory.ThetaSchurBdd.psi_ne_zero hψ _ h1
    · exact hy h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharValuesMemCoeffFieldRange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DeltaRange

theorem delta_value_mem_range : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ), ∃ a : FractionRing (X.O i), ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  intro D N X ρ hρ i j b z
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker : Set (G D.host.E N.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker = (X.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact X.delta_open i
  have : Finite (G D.host.E N.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (X.O i) (FractionRing (X.O i))
    (algebraMap (X.O0 i) (X.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i) σ : (X.O0 i)ˣ) : X.O0 i)), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (X.O0 i) (X.O i))) hopen hσ hn hpow).symm

end GlobalTheory.DeltaRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperLeftBlockEqOneIffOfMemBlockTri
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalLevel

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (h : r = n) (g : GL (Fin n) κ) :
    upperLeftBlock hr g = 1 ↔ g = 1 := by
  subst h
  have hg : g ∈ blockTri (κ := κ) (blk2 r) := fun i j hij => by
    simp [blk2, i.2, j.2] at hij
  constructor
  · intro h1
    apply Units.ext
    ext i j
    have := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ) i j) h1
    simp only [upper_block_val_submatrix hr hg, Matrix.submatrix_apply] at this
    have ei : Fin.castLE hr i = i := Fin.ext rfl
    have ej : Fin.castLE hr j = j := Fin.ext rfl
    rw [ei, ej] at this
    simpa using this
  · rintro rfl
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_lev_whole {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D))
    (L : LevDat D.host.E ℂ n) (hr : L.r = n) (hQ : L.Q = ∅) (hP : L.P.H = ⊥) (x : GL (Fin n) (Lev.EAf D)) :
    x ∈ lev D.sp.cm J β L ↔ x ∈ UA D.sp.cm J ∧ x ∈ St β ∧ ∀ PP ∈ L.Pg, redFn β PP x = 1 := by
  have h0 : ∀ a : Fin n, blkOf L.r L.t a = 0 := fun a => by
    unfold blkOf
    rw [if_pos (by rw [hr]; exact a.2)]
  rw [mem_lev, mem_parLev, hP, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨h1, h2, -, -⟩, h3⟩
    exact ⟨h1, h2, fun PP hPP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).1 (congrFun h3 ⟨PP, hPP⟩)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, fun PP _ i j hij => ?_, fun PP hPP => ?_⟩, funext fun PP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).2 (h3 PP.1 PP.2)⟩
    · rw [h0, h0] at hij
      exact absurd hij (lt_irrefl 0)
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)

theorem levK_eq_levG : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : GlobalTheory.SeriesTie.Setup D.ntw}, GlobalTheory.SeriesTie.RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hpin i j b
  show Lev.levG (Wc D j) (ρ.B i j b).F.βT (Lev.flag1L (ρ.B i j b).G.levT) = _
  rw [hpin.frT i j b]
  unfold Lev.levG
  congr 1
  ext x
  rw [mem_lev_whole _ _ _ rfl rfl rfl, mem_lev_whole _ _ _ (FWT.rank_Wc j).symm rfl rfl]
  have hg : (Lev.flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hpin.Pg i j b
  rw [hg]

end GlobalTheory.PrincipalLevel
end

