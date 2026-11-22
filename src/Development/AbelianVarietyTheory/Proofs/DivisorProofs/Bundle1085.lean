import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
section
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

def toFun {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) :
    IndSp (points (Fin n)) ((ofChar (torusChar χ)).comp (leviTorus (w.adicCompletion E) (Fin n)).symm.toMonoidHom)
      →ₗ[ℂ] (GL (Fin n) (w.adicCompletion E) → ℂ) where
  toFun f := f.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toFun_injective {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) : Function.Injective (toFun w χ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem toFun_intertwines {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (g) (f) :
    toFun w χ (prinSeries χ g f) = rightReg ℂ _ ℂ g (toFun w χ f) := rfl

theorem hasSatGL_prinSeries {n : ℕ} (α : Fin n → ℂˣ) :
    HasSatGL w (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (Finset.univ.val.map α) := by
  have hK : KO (w.adicCompletion E) (Fin n) = KGL w n := SphCompletion.KO_completion w n
  constructor
  · obtain ⟨φ, h, h1, -⟩ := Formalism.UG.Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
    obtain ⟨f, hf, rfl⟩ := (SphCompletion.isSpherical_iff E w n α _).1 h
    refine (Submodule.ne_bot_iff _).2 ⟨f, hK ▸ hf, fun h0 => ?_⟩
    subst h0
    simp at h1
  · intro x hx h0
    have hx' : x ∈ fixed (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (KO (w.adicCompletion E) (Fin n)) :=
      hK ▸ hx
    have hs := (SphCompletion.isSpherical_iff E w n α x.1.1).2 ⟨x, hx', rfl⟩
    exact IsSatVecGL.of_map (toFun w _) (toFun_intertwines w _) (toFun_injective w _)
      (isSatVecGL_of_isSpherical hs fun h => h0 (toFun_injective w _ (h.trans (map_zero _).symm)))

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_parab_one (g : GL (Fin 1) k) : g ∈ parab k (points (Fin 1)) :=
  mem_parab_iff.2 fun a b _ _ hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _)

theorem cB_one (μ : kˣ →* ℂˣ) (p : parab k (points (Fin 1))) :
    PrinProd.cB (fun _ : Fin 1 => μ) p = μ (Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k)) := by
  rw [PrinProd.cB_eq, Fin.prod_univ_one, Fin.prod_univ_one]
  have h : PrinProd.dg p 0 = Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k) := by
    ext
    rw [PrinProd.val_dg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    rfl
  rw [h]
  simp

def oneEquiv (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    (detRep (Fin 1) μ).Equiv (prinSeries fun _ : Fin 1 => μ) := by
  let Ψ : ℂ →ₗ[ℂ] IndSp (points (Fin 1))
      ((ofChar (torusChar fun _ : Fin 1 => μ)).comp (leviTorus k (Fin 1)).symm.toMonoidHom) :=
    { toFun := fun c => ⟨⟨fun g => (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * c, fun p g => by
          show _ = PrinProd.sB (fun _ : Fin 1 => μ) p _
          rw [PrinProd.sB_apply, cB_one]
          beta_reduce
          rw [map_mul, map_mul, Units.val_mul, mul_assoc]⟩,
        MultiIrr.mem_smooth_of_eventually _ (Filter.mem_of_superset
          (IsOpen.mem_nhds (hμ.detChar (n := Fin 1)) (one_mem _)) fun u hu x => by
            have hu' : detChar (Fin 1) μ u = 1 := hu
            show (μ (Matrix.GeneralLinearGroup.det (x * u)) : ℂ) * c = (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * c
            rw [map_mul (Matrix.GeneralLinearGroup.det), map_mul, ← detChar_apply (n := Fin 1) μ u, hu', mul_one])⟩
      map_add' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_add _ _ _))
      map_smul' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_left_comm _ _ _)) }
  refine Representation.Equiv.mk' ⟨Ψ, fun g => LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    (fun F => F.1.1 1) (fun c => ?_) (fun F => Subtype.ext (Subtype.ext (funext fun g => ?_)))
  · show (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * (detRep (Fin 1) μ g c) =
      (μ (Matrix.GeneralLinearGroup.det (x * g)) : ℂ) * c
    simp [detRep, ofChar_apply, mul_assoc]
  · show (μ (Matrix.GeneralLinearGroup.det (1 : GL (Fin 1) k)) : ℂ) * c = c
    simp
  · show (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * F.1.1 1 = F.1.1 g
    have h := parInd_law (points (Fin 1)) _ F ⟨g, mem_parab_one g⟩ 1
    rw [mul_one] at h
    rw [h]
    change _ = PrinProd.sB (fun _ : Fin 1 => μ) ⟨g, mem_parab_one g⟩ _
    rw [PrinProd.sB_apply, cB_one]

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

theorem hasSatGL_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv σ) {B : Multiset ℂˣ} (h : HasSatGL w σ B) : HasSatGL w ρ B := by
  let f : V →ₗ[ℂ] W := e.toLinearEquiv.toLinearMap
  have hi : ∀ g y, f (ρ g y) = σ g (f y) := fun g y => e.toIntertwiningMap.isIntertwining _ _ g y
  have inj : Function.Injective f := e.toLinearEquiv.injective
  constructor
  · obtain ⟨y, hy⟩ := h.exists_vec
    have hfy : f (e.toLinearEquiv.symm y) = y := e.toLinearEquiv.apply_symm_apply y
    have hs : IsSatVecGL w ρ (e.toLinearEquiv.symm y) B := IsSatVecGL.of_map f hi inj (by rw [hfy]; exact hy)
    exact (Submodule.ne_bot_iff _).2 ⟨_, hs.2.1, hs.1⟩
  · intro x hx h0
    have hfx : f x ∈ fixed σ (KGL w n) :=
      GlobalTheory.LGrp.mem_fixed.2 fun g hg => by rw [← hi, GlobalTheory.LGrp.mem_fixed.1 hx g hg]
    exact IsSatVecGL.of_map f hi inj (h.2 _ hfx fun h1 => h0 (inj (h1.trans (map_zero f).symm)))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_unrChar_of_ord {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ} (hϖ : ord k ϖ = 1) :
    χ = unrChar k (χ ϖ) := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  refine MonoidHom.ext fun x => ?_
  have h1 : o (x / ϖ ^ ord k x) = 1 := by
    rw [map_div, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hϖ, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact div_self' _
  have h2 := h _ (ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1))
  rw [map_div, map_zpow, div_eq_one] at h2
  exact h2

theorem ord_unif {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ord (w.adicCompletion E) (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)) = 1 := by
  have h : Valued.v ((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  rw [SphCompletion.ord_completion, h, WithZero.log_exp, neg_neg]

theorem univ_map_two (a b : ℂˣ) : (Finset.univ.val.map ![a, b] : Multiset ℂˣ) = {a, b} := by
  simp [Fin.univ_val_map, List.ofFn_succ]
  rfl

end GlobalTheory.PrinSat

theorem GlobalTheory.PrinSat.hasSatGL_prod₂_detRep : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (μ₁ μ₂ : (w.adicCompletion E)ˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ →
    GlobalTheory.LFun.HasSatGL w (GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin 1) μ₁) (GlobalTheory.SmGL.detRep (Fin 1) μ₂))
      {μ₁ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)), μ₂ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))} := by
  intro E _ _ w μ₁ μ₂ h1 h2
  have e1 := GlobalTheory.PrinSat.eq_unrChar_of_ord h1 (GlobalTheory.PrinSat.ord_unif w)
  have e2 := GlobalTheory.PrinSat.eq_unrChar_of_ord h2 (GlobalTheory.PrinSat.ord_unif w)
  obtain ⟨E1⟩ := GlobalTheory.SmGL.PrinProd.stage_one (fun _ : Fin 1 => μ₁) (fun _ : Fin 1 => μ₂)
  obtain ⟨E2⟩ := GlobalTheory.SmGL.PrinProd.stage_two (fun _ : Fin 1 => μ₁) (fun _ : Fin 1 => μ₂)
  let T := (GlobalTheory.LocGL.prod₂Equiv (GlobalTheory.PrinSat.oneEquiv μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h1))
    (GlobalTheory.PrinSat.oneEquiv μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h2))).trans (E1.trans E2)
  have hA : Fin.append (fun _ : Fin 1 => μ₁) (fun _ : Fin 1 => μ₂) = fun i =>
      GlobalTheory.SmGL.unrChar (w.adicCompletion E) (![μ₁ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)),
        μ₂ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))] i) := by
    funext i
    fin_cases i
    · exact e1
    · exact e2
  have key := GlobalTheory.PrinSat.hasSatGL_prinSeries w ![μ₁ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)),
    μ₂ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))]
  rw [GlobalTheory.PrinSat.univ_map_two, ← hA] at key
  exact GlobalTheory.PrinSat.hasSatGL_of_equiv T key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingSpanEqSpanWords
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem raisingSpan_eq_span_words : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ S : Submodule ℂ H, S ≤ D → raisingSpan ε σ S = (Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}).map D.subtype := by
  intro n ε H _ _ σ D E hK S hSD
  set Y : Set D := {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
    ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hY
  have hcmp := GlobalTheory.T.complexifiedDerivedAction_eq_sum_kFiniteModule n ε H σ D E hK

  have hstab : ∀ a b, ε a = true → ε b = false → ∀ y ∈ Submodule.span ℂ Y, E a b y ∈ Submodule.span ℂ Y := by
    intro a b ha hb y hy
    have hle : Submodule.span ℂ Y ≤ (Submodule.span ℂ Y).comap (E a b) := by
      rw [Submodule.span_le]
      rintro z ⟨l, hl, x, hx, rfl⟩
      apply Submodule.subset_span
      refine ⟨(a, b) :: l, ?_, x, hx, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨ha, hb⟩
        · exact hl p hp
      · simp [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact hle hy
  apply le_antisymm
  · rw [raisingSpan, Submodule.span_le]
    rintro w ⟨l, hl, v, hv, rfl⟩
    have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ pPlus ε) →
        ∃ y ∈ Submodule.span ℂ Y, (y : H) = l.foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) v := by
      intro l
      induction l with
      | nil =>
        intro _
        refine ⟨⟨v, hSD hv⟩, Submodule.subset_span ⟨[], by simp, ⟨v, hSD hv⟩, hv, by simp⟩, rfl⟩
      | cons Z l ih =>
        intro hl
        obtain ⟨y, hy, hyv⟩ := ih (fun Z' hZ' => hl Z' (List.mem_cons_of_mem _ hZ'))
        have hZ := hl Z List.mem_cons_self
        refine ⟨∑ a, ∑ b, Z a b • E a b y, ?_, ?_⟩
        · refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
          by_cases h : ε a = true ∧ ε b = false
          · exact Submodule.smul_mem _ _ (hstab a b h.1 h.2 y hy)
          · rw [hZ a b h, zero_smul]
            exact Submodule.zero_mem _
        · rw [List.foldr_cons, ← hyv, hcmp Z y]
    obtain ⟨y, hy, hyv⟩ := key l hl
    exact ⟨y, hy, hyv⟩
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨y, ⟨l, hl, x, hx, rfl⟩, rfl⟩
    have key : ∀ l : List (Fin n × Fin n),
        (((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x : D) : H) =
          (l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ)).foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) (x : H) := by
      intro l
      induction l with
      | nil => simp
      | cons p l ih =>
        rw [List.map_cons, List.map_cons, List.foldr_cons, ← ih, hcmp, List.prod_cons, Module.End.mul_apply]
        congr 1
        rw [Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
        · simp
        · intro b _ hb; simp [Matrix.single_apply, Ne.symm hb]
        · simp
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ => ?_
          simp [Matrix.single_apply, Ne.symm ha]
        · simp
    refine Submodule.subset_span ⟨l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ), ?_, (x : H), hx, key l⟩
    intro Z hZ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hZ
    exact single_mem_pPlus (hl p hp).1 (hl p hp).2 1

end GlobalTheory.HolDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpen
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.PrincLev

def congGroup {D : D7} (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | GlobalTheory.Member.FinCong V N k}
  one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V N
  mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
  inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha

theorem isOpen_congGroup {D : D7} (V : HSp D) {N : ℕ} (hN : 0 < N) : IsOpen (congGroup V N : Set (GA D V)) :=
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  Subgroup.isOpen_of_mem_nhds _ (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN)

theorem mem_of_isLevelK {D : D7} {V W : HSp D} (hV : V = W) {N : ℕ} {Kf : Subgroup (GA D V)} (hK : IsLevelK V N Kf)
    (k : GA D W) (h1 : k ∈ congGroup W N) (h2 : k ∈ GfC W) : cast (congrArg (GA D) hV.symm) k ∈ Kf := by
  subst hV
  exact (hK k).2 ⟨h2, h1⟩

theorem mem_levG_triv_iff {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    k ∈ levG (Wc D i) (L.βW i) (L.datWp i L.triv) ↔ IsLevelLift (Wc D i) (L.βW i) (L.datWp i L.triv) 1 k :=
  ⟨fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.1 h.2.2⟩, fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.2 h.2.2⟩⟩

theorem levChi_triv_eq_one {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  have h : ∀ x, ext1 L.triv.H L.triv.chi x = 1 := fun x => by
    unfold ext1; split_ifs <;> rfl
  unfold levChi levFn
  simp [LevCh.datWp, datY]
  exact h _

set_option maxHeartbeats 1000000 in

theorem principal_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, (∀ g : GA D (Wc D i), g ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ↔ cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ)) ∧ (∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1) ∧ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ≤ GfC (Wc D i) ∧ ∃ U : Subgroup (GA D (Wc D i)), IsOpen (U : Set (GA D (Wc D i))) ∧ ∀ k ∈ U, k ∈ GfC (Wc D i) → k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL _ ht hpb i σ hσ hV
  have key : ∀ g : GA D (Wc D i), g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ↔
      cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ) := fun g =>
    (mem_levG_triv_iff R.toLevCh i g).trans (GlobalTheory.T.level_character_embedding_compat T R κ v₀ hL ht hpb i (res T σ) hσ hV g)
  have hg : 0 < D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  refine ⟨key, fun k _ => levChi_triv_eq_one R.toLevCh i k, fun k hk => hk.1,
    congGroup (Wc D i) (D.host.g 0 * D.host.g 1), isOpen_congGroup _ hg, fun k h1 h2 => (key k).2 ?_⟩
  exact mem_of_isLevelK hV (ht.laws.levelK _ (inR i) _ hσ) k h1 h2

end GlobalTheory.HolDict.PrincLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionExtendsOverFibreStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_extends_over_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D → genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  IsField Γ(reducedSpecialFibre f, ⊤) →
  (∀ (φ : Z.functionField) (x : Z),
    (∀ z : Z, z ⤳ x → IsDiscreteValuationRing (Z.presheaf.stalk z) → RegAt z φ) → RegAt x φ) →
  ∀ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → UnitAt z (τ i : Z.functionField)) →
  ∀ (M : ℕ) (n : ℤ) (x₀ : Z), 1 ≤ M → x₀ ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → IsDiscreteValuationRing (Z.presheaf.stalk z) →
    RegAt z (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  (∀ i : D.ι, x₀ ∈ D.U i → UnitAt x₀ (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  ∃ gen : (lbPow D M).Gen, gen.IsGen ∧
    ∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
      fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n = (τ i : Z.functionField) ^ M := by
  first | exact @GlobalTheory.PropZCore.gen_of_exponent | exact GlobalTheory.PropZCore.gen_of_exponent | (intros; apply GlobalTheory.PropZCore.gen_of_exponent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBoxLatticesProduct
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan.LeftBasis

theorem isIntB_of_isIntB_of_repr {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) (v : HeightOneSpectrum ℤ)
    (h : ∀ k' k, algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' k') k) ∈ v.adicCompletionIntegers ℚ)
    (y : v.adicCompletion ℚ ⊗[ℚ] M) (hy : IsIntB v b' y) : IsIntB v b y := by
  intro k
  rw [eq_sum_tmul b' v y, map_sum, Finsupp.finset_sum_apply]
  refine sum_mem fun k' _ => ?_
  rw [repr_tmul_apply]
  exact mul_mem (hy k') (h k' k)

theorem isIntB_iff_eventually {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ y, IsIntB v b y ↔ IsIntB v b' y := by
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ' × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h2 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ',
      algebraMap ℚ (v.adicCompletion ℚ) (b'.repr (b t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (h1.and h2)
  refine ⟨hfin.toFinset, fun v hv y => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  exact ⟨isIntB_of_isIntB_of_repr b' b v (fun k k' => hv.2 (k, k')) y,
    isIntB_of_isIntB_of_repr b b' v (fun k' k => hv.1 (k', k)) y⟩

theorem isIntB_sum_leftBasis_iff_eventually : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  intro L _ _ C _ _ ι r e he κ ℓ κ' b
  let Φl : (Fin r → L) →ₗ[ℚ] C :=
    ∑ i, (LinearMap.mulRight ℚ (e i)) ∘ₗ ι.toLinearMap ∘ₗ LinearMap.proj i
  have hΦl : ∀ c, Φl c = ∑ i, ι (c i) * e i := fun c => by
    simp [Φl, LinearMap.sum_apply]
  have hbij : Function.Bijective Φl := by
    refine ⟨fun c c' hcc => ?_, fun x => ?_⟩
    · obtain ⟨d, -, hd⟩ := he (Φl c)
      exact (hd c (hΦl c)).trans (hd c' (hcc.trans (hΦl c'))).symm
    · obtain ⟨d, hd, -⟩ := he x
      exact ⟨d, (hΦl d).trans hd.symm⟩
  let Φ := LinearEquiv.ofBijective Φl hbij
  let b' : Module.Basis (Σ _ : Fin r, κ) ℚ C := (Pi.basis fun _ : Fin r => ℓ).map Φ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  haveI : FiniteDimensional ℚ C := Module.Finite.of_basis b'
  haveI : Fintype κ' := FiniteDimensional.fintypeBasisIndex b
  have hsingle : ∀ (j : Fin r) (l : L), Φ (Pi.single j l) = ι l * e j := by
    intro j l
    show Φl _ = _
    rw [hΦl, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · simp
  have hrepr : ∀ (j : Fin r) (l : L) (i : Fin r) (a : κ),
      b'.repr (ι l * e j) ⟨i, a⟩ = ℓ.repr ((Pi.single j l : Fin r → L) i) a := by
    intro j l i a
    rw [← hsingle]
    simp [b', Module.Basis.map_repr, Pi.basis_repr]
  have hcoord : ∀ (v : HeightOneSpectrum ℤ) (j : Fin r) (z : v.adicCompletion ℚ ⊗[ℚ] L) (i : Fin r) (a : κ),
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
        (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι z * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr ((Pi.single j z : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) i) a := by
    intro v j z i a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s l =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, AlgHom.id_apply,
        repr_tmul_apply, hrepr]
      by_cases h : i = j
      · subst h; simp [repr_tmul_apply]
      · simp [h]
    | add x y hx hy =>
      rw [map_add, add_mul, LinearEquiv.map_add, Finsupp.add_apply, hx, hy, Pi.single_add, Pi.add_apply,
        LinearEquiv.map_add, Finsupp.add_apply]
  obtain ⟨S, hS⟩ := isIntB_iff_eventually b b'
  refine ⟨S, fun v hv β => ?_⟩
  have hy : ∀ (i : Fin r) (a : κ), (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
      (∑ j, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β j) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr (β i) a := by
    intro i a
    rw [map_sum, Finsupp.finset_sum_apply]
    simp_rw [hcoord]
    rw [← Finsupp.finset_sum_apply, ← map_sum]
    congr 2
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hS v hv]
  constructor
  · intro h i a
    rw [← hy]
    exact h ⟨i, a⟩
  · rintro h ⟨i, a⟩
    rw [hy]
    exact h i a

end GlobalTheory.AdicSpan.LeftBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelOfConjInGroupOfCommonFormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_of_conj_in_group_of_common_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' g : G.Cˣ) (s s' sg : ℚ), 0 < s → 0 < s' → 0 < sg → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B → g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' → P.Rel P' := by
  first | (exact @GlobalTheory.RelConj.rel_of_conj_in_form) | (exact GlobalTheory.RelConj.rel_of_conj_in_form) | (intros; apply GlobalTheory.RelConj.rel_of_conj_in_form  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZeroStatement
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringAction_finite_etale_abelianVariety_charZero : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ b : 𝓞 E, b ≠ 0 → IsFinite (act.act b).left ∧ Etale (act.act b).left ∧ Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act b = 1} := by
  first | exact @GlobalTheory.OActFinEt.finite_etale_act | exact GlobalTheory.OActFinEt.finite_etale_act | (intros; apply GlobalTheory.OActFinEt.finite_etale_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roundedTwist_localEquation_chart : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ((p • G + ∑ c, r c • E c) - p • G).Eff ∧ ∀ (i : ι), ∃ ρ : Fin n → ℕ, (∀ j, ρ j < p) ∧ ∀ y ∈ 𝒜.U i, ∀ t, G.IsEqn y t → (p • G + ∑ c, r c • E c).IsEqn y (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j) := by
  first | exact @GlobalTheory.roundedTwist_isEqn | exact GlobalTheory.roundedTwist_isEqn | (intros; apply GlobalTheory.roundedTwist_isEqn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInverseGramLocalBasisIntegralStatement
section
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_inverseGram_localBasis_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (w : HeightOneSpectrum (𝓞 E)), (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x))) → ∀ (X : Matrix (Fin n) (Fin n) E), IsUnit X.det → IsUnit (Xᵀ * J * X.map σ).det → (∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) → ∀ (s : 𝓞 E), s ∉ w.asIdeal → (∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r) → ∀ (e : E), (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) → ∀ i k, w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 := by
  first | exact @GlobalTheory.selfDual_inv_gram_integral | exact GlobalTheory.selfDual_inv_gram_integral | (intros; apply GlobalTheory.selfDual_inv_gram_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupportStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ S : ℝ, ∀ (y : grp G β) (h₁ : G.GAf) (h₂ : Gr G 1), f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S := by
  first | (exact @GlobalTheory.SimBound.main) | (exact GlobalTheory.SimBound.main) | (intros; apply GlobalTheory.SimBound.main  <;> assumption)
end

