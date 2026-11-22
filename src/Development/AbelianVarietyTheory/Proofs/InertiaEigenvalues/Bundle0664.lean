import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0039
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealSideCharacterMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfMemInertia
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem norm_sub_lt_one_of_mem_inertia {l : ℕ} [Fact l.Prime] (K : FinExt l) (σ : ↥(GK K)) (hσ : σ ∈ IK K) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1 := by
  unfold IK at hσ
  induction hσ using Subgroup.closure_induction with
  | mem σ h => exact h
  | one => intro x _; simp
  | mul σ τ _ _ hσ hτ =>
    intro x hx
    have h1 : ‖(τ : GQ l) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have e : ((σ * τ : ↥(GK K)) : GQ l) x - x
        = ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x) := by
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hσ _ h1) (hτ _ hx))
  | inv σ _ hσ =>
    intro x hx
    have h1 : ‖((σ : GQ l)⁻¹) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have h2 := hσ _ h1
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, norm_sub_rev] at h2
    rw [Subgroup.coe_inv]
    exact h2

theorem noTower : NoTower := by
  classical
  intro l _ K N hanti hopen hpow hroot hchar
  have : FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l)) := K.2
  have hGK : IsOpen ((GK K : Subgroup (GQ l)) : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen _
  have hmem : ∀ k (σ : ↥(GK K)), (σ : GQ l) ∈ (N k).map (GK K).subtype ↔ σ ∈ N k := fun k σ =>
    Subgroup.mem_map_iff_mem (GK K).subtype_injective
  obtain ⟨k, hk⟩ := GlobalTheory.T.noDetectedSubgroupTowerRat_proof l (fun k => (N k).map (GK K).subtype)
    (fun i j hij => Subgroup.map_mono (hanti hij))
    (fun k => hGK.isOpenMap_subtype_val _ (hopen k))
    (by
      rintro k _ ⟨σ, hσ, rfl⟩
      exact ⟨σ ^ l, hpow k σ hσ, rfl⟩)
    (by
      rintro j _ ⟨σ, hσ, rfl⟩ h
      exact ⟨σ, hroot j σ hσ ((hmem _ (σ ^ l)).1 h), rfl⟩)
    (by
      intro r
      obtain ⟨k₀, hk₀⟩ := hchar r
      refine ⟨k₀, fun k hk => ?_⟩
      obtain ⟨ι, hι, x, a, h1, h2⟩ := hk₀ k hk
      have key := fun i => GlobalTheory.T.approx_complexPadic_coboundary_algebraic_integer l r ((N k).map (GK K).subtype : Subgroup (GQ l)) (x i)
        (fun σ => if h : σ ∈ GK K then a i ⟨σ, h⟩ else 0) (by
          rintro _ ⟨σ, hσ, rfl⟩
          have := h1 i σ hσ
          simpa using this)
      choose y b hy hb using key
      refine ⟨ι, hι, y, b, fun i σ hσ => hy i σ hσ, ?_⟩
      rintro _ ⟨σ, hσ, rfl⟩ h
      refine ⟨σ, h2 σ hσ fun i => ?_, rfl⟩
      have := hb i _ (h i)
      simpa using this)
  refine ⟨k, fun j σ hσ => ?_⟩
  exact (hmem j σ).1 (hk j _ ((hmem k σ).2 hσ.2) (norm_sub_lt_one_of_mem_inertia K σ hσ.1))

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedJacquetTwoBlocksFinitelyGenerated
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacquetFinGen

theorem span_orbit_eq_top {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : π.IsIrreducible) {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G => π g v) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top
  | exact _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top
  | (apply _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top ..)

theorem jacquet_fg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∃ s : Finset (Jacquet π (unipRad k (two (stdSum h)))),
      Submodule.span ℂ {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ v ∈ s, w = jac₂ (stdSum h) π g v} = ⊤ := by
  intro k _ _ _ _ a b n h V _ _ π hsm hirr
  classical
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set e := stdSum h
  set N := unipRad k (two e)
  have hO := GlobalTheory.SmoothRiesz.finite_orbit π hsm (KO k (Fin n)) (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)) v
  let s : Finset (Jacquet π N) := hO.toFinset.image (Submodule.Quotient.mk (p := twKer π N 1))
  refine ⟨s, ?_⟩
  set T := {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ x ∈ s, w = jac₂ e π g x}
  have key : ∀ g : GL (Fin n) k,
      (Submodule.Quotient.mk (π g v) : Jacquet π N) ∈ Submodule.span ℂ T := by
    intro g
    obtain ⟨p, w, hw, rfl⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (two e) g
    obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k (two e) p
    set m := leviProj k (two e) p
    set y := π w v
    have hy : Submodule.Quotient.mk (p := twKer π N 1) y ∈ s :=
      Finset.mem_image.2 ⟨y, hO.mem_toFinset.2 ⟨w, hw, rfl⟩, rfl⟩
    have hu' : (Submodule.Quotient.mk (π u y) : Jacquet π N) = Submodule.Quotient.mk y := by
      rw [Submodule.Quotient.eq]
      exact Submodule.subset_span ⟨⟨u, hu⟩, y, by simp⟩
    have h1 : π (↑p * w) v = π (leviEmb k (two e) m) (π u y) := by
      rw [hp]; simp only [map_mul, Module.End.mul_apply, y]
    have h2 : (Submodule.Quotient.mk (π (leviEmb k (two e) m) (π u y)) : Jacquet π N) =
        ((deltaHalf k _ m : ℂˣ) : ℂ) • jac₂ e π ((leviTwo k (Fin a) (Fin b)).symm m)
          (Submodule.Quotient.mk y) := by
      show _ = _ • jac (two e) π (leviTwo k (Fin a) (Fin b) ((leviTwo k (Fin a) (Fin b)).symm m)) _
      rw [MulEquiv.apply_symm_apply, ← hu', jac_mk, smul_smul, Units.mul_inv, one_smul]
    rw [h1, h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, hy, rfl⟩)
  have hle : Submodule.span ℂ (Set.range fun g : GL (Fin n) k => π g v) ≤
      (Submodule.span ℂ T).comap (twKer π N 1).mkQ :=
    Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact key g)
  rw [GlobalTheory.JacquetFinGen.span_orbit_eq_top π hirr hv, top_le_iff] at hle
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have : y ∈ (Submodule.span ℂ T).comap (twKer π N 1).mkQ := hle ▸ Submodule.mem_top
  exact this

end GlobalTheory.JacquetFinGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalHomExtBreuilKisinPrism
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

theorem FHom.ext_u {M M' : FCrys l R} {u u' : FHom M M'} (h : ∀ P, u.u P = u'.u P) : u = u' := by
  cases u; cases u'
  congr
  funext P
  exact h P

theorem FHom.eq_of_tr {M M' : FCrys l R} (u u' : FHom M M') {P Q : Obj l R} (g : Hom P Q)
    (hP : u.u P = u'.u P) : u.u Q = u'.u Q := by
  let v : M.M P →ₛₗ[g.f] M'.M Q := (M'.tr g).comp (u.u P)
  obtain ⟨w, -, hw⟩ := M.tr_bc g (M'.M Q) v
  have h1 := hw (u.u Q) fun x => by simp [v, u.u_tr]
  have h2 := hw (u'.u Q) fun x => by simp [v, u'.u_tr, hP]
  rw [h1, h2]

theorem FHom.eq_of_inj {M M' : FCrys l R} (u u' : FHom M M') {B C : Obj l R} (h : Hom B C)
    (hinj : Function.Injective h.f) (hC : u.u C = u'.u C) : u.u B = u'.u B := by
  haveI := M'.fin B
  haveI := M'.proj B
  have hi : Function.Injective (M'.tr h) :=
    semiBC_injective_of_injective _ _ h.f hinj _ _ (M'.tr h) (M'.tr_bc h)
  ext x
  apply hi
  rw [← u.u_tr, ← u'.u_tr, hC]

theorem fhom_ext_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K))
    (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  intro l _ K bk M M' u u' hbk
  apply FHom.ext_u
  intro B
  obtain ⟨C, h, ⟨g⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hC := FHom.eq_of_tr u u' g hbk
  exact FHom.eq_of_inj u u' h (GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc).1 hC

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageUnipotentBlockColumnTransformEqZe
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric.ColSplit

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem mem_ratV_iff {ι : Type} (x : ι → Ad E) : x ∈ ratV E ι ↔ ∀ t, ∃ c : E, algebraMap E (Ad E) c = x t := by
  constructor
  · rintro ⟨c, rfl⟩ t
    exact ⟨c t, rfl⟩
  · intro h
    choose c hc using h
    exact ⟨c, funext hc⟩

variable (E) in

def reix {ι κ : Type} (τ : κ ≃ ι) : (κ → Ad E) ≃ₜ+ (ι → Ad E) where
  toFun w := w ∘ τ.symm
  invFun x := x ∘ τ
  left_inv w := by funext t; simp
  right_inv x := by funext t; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem reix_mem {ι κ : Type} (τ : κ ≃ ι) (w : κ → Ad E) : reix E τ w ∈ ratV E ι ↔ w ∈ ratV E κ := by
  simp only [mem_ratV_iff]
  change (∀ t, ∃ c : E, algebraMap E (Ad E) c = w (τ.symm t)) ↔ _
  exact ⟨fun h s => by simpa using h (τ s), fun h t => h _⟩

theorem per_reix {ι κ : Type} (τ : κ ≃ ι) {Φ : (ι → Ad E) → ℂ} (h : Per (ratV E ι) Φ) :
    Per (ratV E κ) (fun w => Φ (w ∘ τ.symm)) := by
  refine ⟨h.1.comp (reix E τ).continuous, fun γ hγ w => ?_⟩
  have := h.2 (reix E τ γ) ((reix_mem τ γ).2 hγ) (reix E τ w)
  exact this

theorem avg_reix {ι κ : Type} [Fintype ι] [Fintype κ] (τ : κ ≃ ι) {Φ : (ι → Ad E) → ℂ} (h : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = avg (ratV E κ) (fun w => Φ (w ∘ τ.symm)) :=
  (GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ _ _ (isCoLat_ratV E κ) (isCoLat_ratV E ι) (reix E τ) (reix_mem τ) Φ h).symm

theorem avg_sum_reix {ι κ₁ κ₂ : Type} [Fintype ι] [Fintype κ₁] [Fintype κ₂] (τ : κ₁ ⊕ κ₂ ≃ ι)
    {Φ : (ι → Ad E) → ℂ} (h : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = avg (ratV E κ₁) (fun z => avg (ratV E κ₂) (fun y => Φ (Sum.elim z y ∘ τ.symm))) := by
  rw [avg_reix τ h]
  exact GlobalTheory.T.quotientAverage_sum_index_fubini E κ₁ κ₂ _ (per_reix τ h)

end Gen

end GlobalTheory.CuspGeneric.ColSplit

namespace GlobalTheory.CuspGeneric.ColSplit

section Main

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem sumElim_add_left {κ₁ κ₂ : Type} (c : κ₁ → E) (n : κ₁ → Ad E) (w : κ₂ → Ad E) :
    Sum.elim ((fun t => algebraMap E (Ad E) (c t)) + n) w =
      (fun s => algebraMap E (Ad E) (Sum.elim c 0 s)) + Sum.elim n w := by
  funext s; cases s <;> simp

theorem sumElim_add_right {κ₁ κ₂ : Type} (c : κ₂ → E) (n : κ₁ → Ad E) (w : κ₂ → Ad E) :
    Sum.elim n ((fun t => algebraMap E (Ad E) (c t)) + w) =
      (fun s => algebraMap E (Ad E) (Sum.elim 0 c s)) + Sum.elim n w := by
  funext s; cases s <;> simp

theorem blk_rat {r' m' : ℕ} {κ : Type} [Fintype κ] (σ : κ ≃ UnipotentBlockColumnIndex a r' m') {f : GA E a → ℂ}
    (hl : ∀ (c : UnipotentBlockColumnIndex a r' m' → E) g, f (ratGL E a (blkU c) * g) = f g) (c : κ → E) (v : κ → Ad E) (h : GA E a) :
    f (blkU (((fun t => algebraMap E (Ad E) (c t)) + v) ∘ σ.symm) * h) = f (blkU (v ∘ σ.symm) * h) := by
  have e : blkU (((fun t => algebraMap E (Ad E) (c t)) + v) ∘ σ.symm) =
      ratGL E a (blkU (c ∘ σ.symm)) * blkU (v ∘ σ.symm) := by
    rw [ratGL_blkU]
    exact posU_add _ _ _
  rw [e, mul_assoc, hl]

theorem continuous_sumElim_right {κ₁ κ₂ : Type} (n : κ₁ → Ad E) :
    Continuous fun w : κ₂ → Ad E => Sum.elim n w :=
  continuous_pi fun s => match s with
    | Sum.inl _ => continuous_const
    | Sum.inr l => continuous_apply l

theorem continuous_sumElim {κ₁ κ₂ : Type} : Continuous fun p : (κ₁ → Ad E) × (κ₂ → Ad E) => Sum.elim p.1 p.2 :=
  continuous_pi fun s => match s with
    | Sum.inl l => (continuous_apply l).comp continuous_fst
    | Sum.inr l => (continuous_apply l).comp continuous_snd

theorem per_position {r' m' : ℕ} {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂] (σ : κ₁ ⊕ κ₂ ≃ UnipotentBlockColumnIndex a r' m')
    {f : GA E a → ℂ} (hc : Continuous f) (hl : ∀ (c : UnipotentBlockColumnIndex a r' m' → E) g, f (ratGL E a (blkU c) * g) = f g)
    (n : κ₁ → Ad E) (h : GA E a) : Per (ratV E κ₂) (fun w => f (blkU (Sum.elim n w ∘ σ.symm) * h)) := by
  refine ⟨hc.comp (((continuous_posU _).comp ((reix E σ).continuous.comp (continuous_sumElim_right n))).mul
    continuous_const), ?_⟩
  rintro _ ⟨c, rfl⟩ w
  change f (blkU (Sum.elim n ((fun t => algebraMap E (Ad E) (c t)) + w) ∘ σ.symm) * h) = _
  rw [sumElim_add_right, blk_rat σ hl]

theorem dot_col {r m : ℕ} (hr : r ≤ m) (z : HiIx a r (m + 1) → Ad E) (y : LoIx a r (m + 1) → Ad E) :
    dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) =
      dot (eLast a (m + 1)) (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : r ≤ (t.1.1 : ℕ)
  · have e : (colEquiv a r (m + 1)).symm t = Sum.inl ⟨t, h⟩ := Equiv.sumCompl_symm_apply_of_pos (p := fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => r ≤ (t.1.1 : ℕ)) h
    simp only [Function.comp, e, Sum.elim_inl]
  · have : (eLast a (m + 1) t : E) = 0 := by
      simp only [eLast]
      rw [if_neg]
      omega
    simp [this]

theorem colT_avg_blk_eq_zero (hψ : StdPsi ψ) (m : ℕ) (f : GA E a → ℂ) (hf : Good ψ (m + 1) f)
    (r : ℕ) (h0 : 0 < r) (hr : r ≤ m) (g : GA E a) :
    avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => colT ψ (m + 1) f (blkU n * g)) = 0 := by
  have hr1 : r ≤ m + 1 := by omega
  have hl : ∀ {r' : ℕ} (c : UnipotentBlockColumnIndex a r' (m + 1) → E) g, f (ratGL E a (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g

  have hA : ∀ n : UnipotentBlockColumnIndex a r m → Ad E, colT ψ (m + 1) f (blkU n * g) =
      avg (ratV E (HiIx a r (m + 1))) (fun z => avg (ratV E (LoIx a r (m + 1))) (fun y =>
        ψ (-dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * (blkU n * g)))) := by
    intro n
    unfold colT coefF
    exact avg_sum_reix (colEquiv a r (m + 1)) (per_coef hψ _ hf.cont hl _)
  have hB : ∀ (n : UnipotentBlockColumnIndex a r m → Ad E) (z : HiIx a r (m + 1) → Ad E),
      avg (ratV E (LoIx a r (m + 1))) (fun y =>
        ψ (-dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * (blkU n * g))) =
      ψ (-dot (eLast a (m + 1)) (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm)) *
        avg (ratV E (LoIx a r (m + 1))) (fun w => f (blkU (Sum.elim n w ∘ (blkEquiv a r m hr1).symm) *
          (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g))) := by
    intro n z
    have e : ∀ y : LoIx a r (m + 1) → Ad E,
        ψ (-dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * (blkU n * g)) =
        ψ (-dot (eLast a (m + 1)) (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim n (y + -corr n z) ∘ (blkEquiv a r m hr1).symm) *
            (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g)) := by
      intro y
      rw [dot_col hr, ← mul_assoc, blkU_col_mul_blkU hr1, mul_assoc, sub_eq_add_neg]
    simp_rw [e]
    rw [avg_const_mul]
    exact congrArg _ (GlobalTheory.T.quotientAverage_translate_invariant _ _ (isCoLat_ratV _ _)
      (fun w => f (blkU (Sum.elim n w ∘ (blkEquiv a r m hr1).symm) *
          (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g)))
      (per_position (blkEquiv a r m hr1) hf.cont hl n _) (-corr n z))

  obtain ⟨Φ₂, hΦ₂⟩ : ∃ Φ₂ : (UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E) → ℂ, ∀ p, Φ₂ p =
      avg (ratV E (LoIx a r (m + 1))) (fun y =>
        ψ (-dot (eLast a (m + 1)) (Sum.elim p.2 y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim p.2 y ∘ (colEquiv a r (m + 1)).symm) * (blkU p.1 * g))) := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : (UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E) → ℂ, ∀ p, H p =
      avg (ratV E (LoIx a r (m + 1))) (fun w => f (blkU (Sum.elim p.1 w ∘ (blkEquiv a r m hr1).symm) *
          (blkU (Sum.elim p.2 0 ∘ (colEquiv a r (m + 1)).symm) * g))) := ⟨_, fun _ => rfl⟩
  have hΦH : ∀ p, Φ₂ p = ψ (-dot (eLast a (m + 1)) (Sum.elim p.2 0 ∘ (colEquiv a r (m + 1)).symm)) * H p := by
    intro p
    rw [hΦ₂, hH, hB]
  have hHc : Continuous H := by
    have e : H = fun p => avg (ratV E (LoIx a r (m + 1))) (fun w =>
        (fun q : ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E)) × (LoIx a r (m + 1) → Ad E) =>
          f (blkU (Sum.elim q.1.1 q.2 ∘ (blkEquiv a r m hr1).symm) *
            (blkU (Sum.elim q.1.2 0 ∘ (colEquiv a r (m + 1)).symm) * g))) (p, w)) := funext hH
    rw [e]
    refine GlobalTheory.T.continuous_quotientAverage_periodic_family (LoIx a r (m + 1) → Ad E) (ratV E (LoIx a r (m + 1))) (isCoLat_ratV E _)
      ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E))
      (fun q => f (blkU (Sum.elim q.1.1 q.2 ∘ (blkEquiv a r m hr1).symm) *
            (blkU (Sum.elim q.1.2 0 ∘ (colEquiv a r (m + 1)).symm) * g))) ?_ ?_
    · have c₁ : Continuous fun q : ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E)) × (LoIx a r (m + 1) → Ad E) =>
          Sum.elim q.1.1 q.2 := continuous_sumElim.comp (continuous_fst.fst.prodMk continuous_snd)
      have c₂ : Continuous fun q : ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E)) × (LoIx a r (m + 1) → Ad E) =>
          Sum.elim q.1.2 (0 : LoIx a r (m + 1) → Ad E) :=
        continuous_sumElim.comp (continuous_fst.snd.prodMk continuous_const)
      exact hf.cont.comp (((continuous_posU _).comp ((reix E (blkEquiv a r m hr1)).continuous.comp c₁)).mul
        (((continuous_posU _).comp ((reix E (colEquiv a r (m + 1))).continuous.comp c₂)).mul continuous_const))
    · intro x γ hγ y
      exact (per_position (blkEquiv a r m hr1) hf.cont hl x.1 _).2 γ hγ y
  have hψc : Continuous fun p : (UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E) =>
      ψ (-dot (eLast a (m + 1)) (Sum.elim p.2 0 ∘ (colEquiv a r (m + 1)).symm)) :=
    hψ.cont.comp ((continuous_dot _).comp ((reix E (colEquiv a r (m + 1))).continuous.comp
      (continuous_sumElim.comp (continuous_snd.prodMk continuous_const)))).neg
  have hPer : Per ((ratV E (UnipotentBlockColumnIndex a r m)).prod (ratV E (HiIx a r (m + 1)))) Φ₂ := by
    refine ⟨?_, ?_⟩
    · rw [funext hΦH]
      exact hψc.mul hHc
    · intro γ hγ p
      rw [AddSubgroup.mem_prod] at hγ
      obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := hγ
      have e₁ : γ.1 = fun t => algebraMap E (Ad E) (c₁ t) := hc₁.symm
      have e₂ : γ.2 = fun t => algebraMap E (Ad E) (c₂ t) := hc₂.symm
      have s₁ : Φ₂ (γ + p) = Φ₂ (p.1, γ.2 + p.2) := by
        rw [show γ + p = (γ.1 + p.1, γ.2 + p.2) from rfl, hΦH, hΦH]
        congr 1
        rw [hH, hH]
        congr 1
        funext w
        change f (blkU (Sum.elim (γ.1 + p.1) w ∘ _) * _) = _
        rw [e₁, sumElim_add_left, blk_rat _ hl]
      have s₂ : Φ₂ (p.1, γ.2 + p.2) = Φ₂ p := by
        rw [hΦ₂, hΦ₂]
        congr 1
        funext y
        change ψ (-dot _ (Sum.elim (γ.2 + p.2) y ∘ _)) * f (blkU (Sum.elim (γ.2 + p.2) y ∘ _) * _) = _
        have hm := hψ.map_dot (eLast a (m + 1)) (Sum.elim c₂ 0 ∘ (colEquiv a r (m + 1)).symm)
          (Sum.elim p.2 y ∘ (colEquiv a r (m + 1)).symm)
        rw [e₂, sumElim_add_left, blk_rat _ hl, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv]
        congr 1
        exact congrArg _ hm
      rw [s₁, s₂]
  have hD : ∀ z : HiIx a r (m + 1) → Ad E, avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => Φ₂ (n, z)) = 0 := by
    intro z
    simp_rw [hΦH]
    rw [avg_const_mul]
    have e : avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => H (n, z)) =
        avg (ratV E (UnipotentBlockColumnIndex a r (m + 1))) (fun w => f (blkU w * (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g))) := by
      rw [avg_sum_reix (blkEquiv a r m hr1) (per_blk hf.cont hl _)]
      simp_rw [hH]
    rw [e, hf.van r h0 hr1, mul_zero]
  have hA' : (fun n => colT ψ (m + 1) f (blkU n * g)) = fun n => avg (ratV E (HiIx a r (m + 1))) (fun z => Φ₂ (n, z)) := by
    funext n
    rw [hA]
    simp_rw [hΦ₂]
  rw [hA', GlobalTheory.T.quotientAverage_adelicRationalPoints_comm E _ _ Φ₂ hPer]
  simp_rw [hD]
  simpa using avg_const_mul (ratV E (HiIx a r (m + 1))) 0 (fun _ => (1 : ℂ))

end Main

theorem _root_.GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ),
    StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ r, 0 < r → r ≤ m → ∀ g : GA E a,
      avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => colT ψ (m + 1) f (blkU n * g)) = 0 :=
  fun _ _ _ _ _ hψ m f _ hf r h0 hr g => colT_avg_blk_eq_zero hψ m f hf r h0 hr g

end GlobalTheory.CuspGeneric.ColSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatMatExists
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCharChange
open Formalism.IndefR.Lev

theorem ratMat_exists {D : D7} (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  have h := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨γE, -, e⟩ := Subgroup.mem_map.1 h
  exact ⟨γE, e.symm⟩

theorem flag_vals {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (hcg : ∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ))
    (hxq : ∀ PP ∈ L.Q, ∀ x, ∃ a, D.what₂.embLL a = ((L.xq PP x : ℂˣ) : ℂ)) (x) :
    ∃ a, D.what₂.embLL a = ((levFn β (flagL L) x : ℂˣ) : ℂ) := by
  have h1 : (flagL L).P.chi = 1 := rfl
  unfold levFn
  rw [h1, subgroupCharExtension_one_apply, one_mul]
  refine RingHom.mem_fieldRange.1 ?_
  simp only [Units.val_mul, Units.coe_prod]
  refine Subfield.mul_mem _ (Subfield.prod_mem _ fun PP hP => Subfield.prod_mem _ fun j hj => ?_)
    (Subfield.prod_mem _ fun PP hP => ?_)
  · obtain ⟨a, ha⟩ := hcg j (Finset.mem_range.1 hj) PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩
  · obtain ⟨a, ha⟩ := hxq PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩

end GlobalTheory.TwistCharChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : Bst P), (∀ g : ↥(GK K), actSt P (g : GQ l) x = x) ↔ ∃ c : ↥(K0 K), x = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
  first | exact @GlobalTheory.PMon.stInv_iff | exact GlobalTheory.PMon.stInv_iff | (intros; apply GlobalTheory.PMon.stInv_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumEqAlternatingSumStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedInvolutionStableLatticeSum_eq_alternating_sum : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι), B.LieReg → IsFrame B e π S → ∀ I ⊆ S, ∀ u : B.A, IsUnit u → HH B π I (S \ I) u 1 = ∑ J ∈ S.powerset, (-1 : ℚ) ^ (J ∩ I).card * B.GG ((∏ j ∈ J, π j) * u) := by
  first | exact @GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG | exact GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG | (intros; apply GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumProductSubFactorsStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_signedLatticeSum_product_sub_factors : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O), B₁.LieReg → B₂.LieReg → (B₁.P * B₂.P).Separable → K.Small a → IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → Tendsto (fun k : ℕ => (((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 - (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) : ℚ) : ℝ) / ((B₁.rho (algebraMap K.O B₁.A a ^ k) : ℝ) * (B₂.rho (algebraMap K.O B₂.A a ^ k) : ℝ)))) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | exact GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | (intros; apply GlobalTheory.UnitLemma.Desc.hh_prod_tendsto <;> assumption)
end

