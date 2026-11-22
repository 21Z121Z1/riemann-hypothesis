import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0791
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0281
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0027
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0001
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
import Batteries.Tactic.OpenPrivate

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ConjTor
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

namespace UpperTheory.V.Z.Ord

section Loc

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

private theorem hasSupport_contra {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL k)} (h : HasSupport π s) :
    HasSupport (contra π) (s.map Zc.dualCl) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨m, x, hs, hirr, hcusp, e, hsub⟩ := h
  have hπs : GlobalTheory.PRep.IsSmooth π := HasSupport.isSmooth ⟨m, x, hs, hirr, hcusp, e, hsub⟩
  have key : IsCuspSupport (contra π) (fun a => (x a).fst) (fun a => contra (x a).rep) := by
    refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N)
      (hA k N V π hπs hirr) hirr, fun a => ?_, e, ?_⟩
    · have hc := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA (x a) ⟨(hcusp a).1, (hcusp a).2.2⟩).1
      rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA, IrrGL.isCusp_of] at hc
      exact ⟨(hcusp a).1, GlobalTheory.CompanionTheory.ContraProd.contra_rep_isIrreducible hA (x a), hc.2⟩
    · have hρs : GlobalTheory.PRep.IsSmooth (piTensor fun a => (x a).rep) :=
        isSmooth_piTensor fun a => (x a).snd.rep.smooth
      have h1 := GlobalTheory.CompanionTheory.ContraSub.main k N V _ π (parInd e (piTensor fun a => (x a).rep)) hπs
        (isSmooth_parInd e _) hsub
      have h2 : Nonempty ((parInd e (piTensor fun a => contra (x a).rep)).Equiv
          (contra (parInd e (piTensor fun a => (x a).rep)))) :=
        GlobalTheory.CompanionTheory.ContraProd.parInd_equiv_contra (σ := piTensor fun a => contra (x a).rep)
          (ρ := piTensor fun a => (x a).rep) e hρs (GlobalTheory.CompanionTheory.ContraProd.contra_piTensor_rep hA x)
      obtain ⟨E⟩ := h2
      have h3 : IsSubquotient (contra (parInd e (piTensor fun a => (x a).rep)))
          (parInd e (piTensor fun a => contra (x a).rep)) :=
        IsSubquotient.of_surjective E.toIntertwiningMap fun w => ⟨E.invFun w, E.right_inv w⟩
      exact IsSubquotient.trans h1 h3
  have hsupp := hasSupport_of_isCuspSupport key
  have hmap : s.map Zc.dualCl = Multiset.map (fun a => Zc.dualCl (x a)) Finset.univ.val := by
    rw [← hs, Multiset.map_map]
    rfl
  rw [hmap]
  simp only [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  exact hsupp

private theorem hasSupport_of_invT (c : k ≃+* k') (hc : Continuous c) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) V) (τ : Representation ℂ (GL (Fin N) k') W)
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g v, τ (GlobalTheory.LFun.ConjPlace.invT c N g) (T v) = T (σ g v))
    {s : Multiset (IrrGL k)} (h : HasSupport σ s) :
    HasSupport τ ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL c (GlobalTheory.LocalFieldIso.continuous_symm c hc))) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hc' := GlobalTheory.LocalFieldIso.continuous_symm c hc
  obtain ⟨E⟩ := GlobalTheory.GelfandKazhdan.equiv_contra k N V σ (hA k N V σ h.isSmooth h.isIrreducible) h.isIrreducible
  have h1 := (hasSupport_contra h).of_equiv E.symm
  have h2 := GlobalTheory.SuppIne.hasSupport_comp c hc hc' h1
  refine h2.of_equiv (GlobalTheory.LocGL.equivOfBijective ⟨T.toLinearMap, fun g => LinearMap.ext fun v => ?_⟩ T.bijective)
  have hg : GlobalTheory.LFun.ConjPlace.invT c N (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k
      (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) = g :=
    Units.ext (Matrix.ext fun i j => by
      rw [GlobalTheory.LFun.ConjPlace.invT_val]
      exact c.apply_symm_apply _)
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change T (σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) v) = τ g (T v)
  rw [← hT, hg]

private theorem dualCl_eq_of {x y : IrrGL k} (H : GlobalTheory.LocLanglands.DualCl x y) : Zc.dualCl x = y := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨n, π, π', rfl, rfl, ⟨E⟩⟩ := H
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  change IrrGL.of _ _ _ = IrrGL.of π'.ρ π'.smooth π'.irr
  exact IrrGL.of_eq_of.2 ⟨(GlobalTheory.ContraRefl.contraEquiv (equivRep π)).trans E.symm⟩

private theorem val_lt_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) < 1 ↔ valuation k x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x⁻¹
  have p1 : 0 < valuation k x := by
    rw [zero_lt_iff]; simpa using hx
  have p2 : 0 < valuation k' (i x) := by
    rw [zero_lt_iff]; simpa using hx
  rw [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ p1, inv_le_one₀ p2] at h
  rw [← not_le, ← not_le, h]

private theorem val_eq_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) = 1 ↔ valuation k x = 1 := by
  have a := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x
  have b := val_lt_one_iff i hi x
  exact ⟨fun h => le_antisymm (a.1 h.le) (not_lt.1 fun l => (b.2 l).ne h),
    fun h => le_antisymm (a.2 h.le) (not_lt.1 fun l => (b.1 l).ne h)⟩

private theorem unram_unif (i : k ≃+* k') (hi : Continuous i) (μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    μ (Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k')) = μ (ImaginaryQuadraticEtaCharacter.unif k) := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  set a : kˣ := Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k') with ha
  have hav : (a : k) = i.symm (ImaginaryQuadraticEtaCharacter.unif k' : k') := rfl
  have S := (ImaginaryQuadraticEtaCharacter.polFacts k).1
  have S' := (ImaginaryQuadraticEtaCharacter.polFacts k').1
  have ha1 : valuation k (a : k) < 1 := by
    rw [hav]; exact (val_lt_one_iff i.symm hi' _).2 S'.1
  have hb1 : valuation k' (i (ImaginaryQuadraticEtaCharacter.unif k : k)) < 1 := (val_lt_one_iff i hi _).2 S.1
  have le1 := S.2 _ ha1
  have le2 := S'.2 _ hb1
  have pa : 0 < valuation k (a : k) := by
    rw [zero_lt_iff]; simp
  have pb : 0 < valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := by
    rw [zero_lt_iff]; simp
  have pu : 0 < valuation k' (ImaginaryQuadraticEtaCharacter.unif k' : k') := by
    rw [zero_lt_iff]; simp
  have le3 : valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) ≤ valuation k (a : k) := by
    have h1 : valuation k' (i ((ImaginaryQuadraticEtaCharacter.unif k : k) * (a : k)⁻¹)) ≤ 1 := by
      have : i (a : k) = (ImaginaryQuadraticEtaCharacter.unif k' : k') := by rw [hav]; exact i.apply_symm_apply _
      rw [map_mul, map_inv₀, this, map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ le2 zero_le'
    have h2 := (GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi _).1 h1
    rw [map_mul, map_inv₀] at h2
    simpa using (mul_inv_le_iff₀ pa).1 h2
  have he : valuation k (a : k) = valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := le_antisymm le1 le3
  have hu : μ (a * (ImaginaryQuadraticEtaCharacter.unif k)⁻¹) = 1 := hμ _ (by
    rw [Units.val_mul, map_mul, he, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ pb.ne'])
  rw [map_mul, map_inv, mul_inv_eq_one] at hu
  exact hu

private theorem isUnram_comp (i : k ≃+* k') (hi : Continuous i) {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) :
    IsUnram (μ.comp (Units.map i.symm.toRingHom.toMonoidHom)) := fun x hx =>
  hμ _ ((val_eq_one_iff i.symm (GlobalTheory.LocalFieldIso.continuous_symm i hi) _).2 hx)

private theorem unl_of_map (i : k ≃+* k') (hi : Continuous i) (q : ℕ) (s : Multiset (IrrGL k))
    (h : ImaginaryQuadraticEtaCharacter.Unl q ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i (GlobalTheory.LocalFieldIso.continuous_symm i hi)))) :
    ImaginaryQuadraticEtaCharacter.Unl q s := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  intro ξ hξ ξ' hξ' hun
  obtain ⟨h1, m1⟩ := hξ
  obtain ⟨h2, m2⟩ := hξ'
  let U : k'ˣ →* kˣ := Units.map i.symm.toRingHom.toMonoidHom
  have sm : ∀ ζ : kˣ →* ℂˣ, IsSmoothChar ζ → IsSmoothChar ((ζ⁻¹).comp U) := fun ζ hζ =>
    IsOpen.preimage (Continuous.units_map _ hi') hζ.inv
  have mem : ∀ (ζ : kˣ →* ℂˣ) (hζ : IsSmoothChar ζ), IrrGL.ofChar ζ hζ ∈ s →
      IrrGL.ofChar ((ζ⁻¹).comp U) (sm ζ hζ) ∈ (s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i hi') := fun ζ hζ hm =>
    Multiset.mem_map.2 ⟨IrrGL.ofChar ζ⁻¹ hζ.inv, Multiset.mem_map.2 ⟨_, hm,
      dualCl_eq_of (GlobalTheory.LocLanglands.CuspModel.dualCl_ofChar _ _ hζ hζ.inv rfl)⟩,
      GlobalTheory.DegOneChar.trGL_ofChar i hi' _ _ _⟩
  have e : ((ξ'⁻¹).comp U) * ((ξ⁻¹).comp U)⁻¹ = (ξ * ξ'⁻¹).comp U :=
    MonoidHom.ext fun x => by simp [mul_comm]
  have := h ((ξ'⁻¹).comp U) ⟨sm _ h2, mem _ _ m2⟩ ((ξ⁻¹).comp U) ⟨sm _ h1, mem _ _ m1⟩
    (by rw [e]; exact isUnram_comp i hi hun)
  rw [e, MonoidHom.comp_apply] at this
  rwa [unram_unif i hi _ hun] at this

end Loc

end UpperTheory.V.Z.Ord
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.FlagJ
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Ord

def FlagJ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (J : Ideal B.B),
    B.RingProps Λ J → ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h → x.IsRep ρ →
    Af.IsIrr ρ → ∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)

def BornJ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (J : Ideal B.B), B.RingProps Λ J → ENDO B ι J →
    ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h →
    x.IsRep ρ → Af.IsIrr ρ → Continuous ρ → ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → Win.Unl1 ρ w →
      Win.PotUnl ρ w ∧ ∀ π : CuspSub L n, Af.AttC ι ρ π → TU π w

end UpperTheory.V.Z.Ord

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.OrdJac
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

open private UpperTheory.V.Hi.OrdB.inv_inj UpperTheory.V.Hi.OrdB.exists_form UpperTheory.V.Hi.OrdB.num UpperTheory.V.Hi.OrdB.tc_single from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsNil

theorem UpperTheory.V.Z.Ord.ordJac :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → OrdJac := by
  intro H k _ _ _ _ n V _ _ π hπ hirr c φ hφ0 v hv hv0 a ha
  obtain ⟨hker, hsm, hI, -, -, -, -, hidx, hz, hT⟩ := glBridge k n V π
  have hφ : ∀ t : (glIwa k n).T, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → φ t = 1 := fun t ht => by
    obtain ⟨y, hy, hy'⟩ := hT t
    have e : (t : GL (Fin n) k) ∈ φ.ker.map (glIwa k n).T.subtype := by
      rw [hy]
      refine list_prod_mem fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact ⟨eT k n i (y i), hφ0 i _ (hy' c ht i), rfl⟩
    obtain ⟨s, hs, e⟩ := e
    exact (Subtype.ext e : s = t) ▸ hs
  haveI : FiniteDimensional ℂ (fixd π ((glIwa k n).I1 c)) := by
    have hfix : fixd π ((glIwa k n).I1 c) = fixed π ((glIwa k n).I1 c) := by
      ext w
      exact ⟨fun h u => by simpa using h u u.2, fun h u hu => by simpa using h ⟨u, hu⟩⟩
    rw [hfix]
    exact ((H.loc.bz k).1 _ V π hπ hirr).2 _ (hI c).1 (hI c).2
  let p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n)) := Submodule.mkQ _
  have hp : ∀ t w, jacB π t (p w) =
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) w) :=
    fun t w => UnramFixed.jacB_apply π t _
  have hlist : ∀ s : List ℕ, (∀ j ∈ s, j < n) → (s.map (al k n)).prod ∈ (glIwa k n).P ∧
      ∃ b : ℂ, b ≠ 0 ∧ (glIwa k n).uOp π (s.map (al k n)).prod v = b • v := by
    intro s
    induction s with
    | nil =>
      exact fun _ => ⟨one_mem _, 1, one_ne_zero, by
        simpa using (uOpMul _ (glIwa k n) ℂ V π 1 1 (one_mem _) (one_mem _) v hv.1).2.2.1⟩
    | cons j s ih =>
      intro hs
      obtain ⟨hP, b, hb, h2⟩ := ih fun i hi => hs i (List.mem_cons_of_mem _ hi)
      rw [List.map_cons, List.prod_cons]
      refine ⟨mul_mem (al_mem k n j) hP, ?_⟩
      rcases j with _ | j
      · have e : al k n 0 = 1 := by
          rw [al, upow, ← (diagT k (Fin n)).map_one]; congr 1; funext i; simp
        rw [e, one_mul]
        exact ⟨b, hb, h2⟩
      · have hj := ha ⟨j, by have := hs _ List.mem_cons_self; omega⟩
        refine ⟨a (j + 1) * b, mul_ne_zero hj.1 hb, ?_⟩
        rw [← (uOpMul _ (glIwa k n) ℂ V π _ _ (al_mem k n _) hP v hv.1).2.1, h2, map_smul]
        have e := hj.2
        simp only at e
        rw [e, smul_smul, mul_comm]
  obtain ⟨-, b, hb, hzb⟩ := hlist (List.range n) fun j hj => List.mem_range.1 hj
  rw [← hz] at hzb
  have hpow : ∀ j : ℕ, ((glIwa k n).uOp π (glIwa k n).z ^ j) v = b ^ j • v := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hzb, smul_smul, pow_succ]
  have hvi : v ∈ invPart π c φ := (Submodule.mem_iInf _).2 fun j =>
    ⟨(b ^ j)⁻¹ • v, Submodule.smul_mem _ _ hv, by
      rw [map_smul, hpow, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hb), one_smul]⟩
  have hx0 : p v ≠ 0 := fun h => hv0 (UpperTheory.V.Hi.OrdB.inv_inj _ π c φ hφ (hsm hπ) hvi
    (hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h))
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨μ, hμs, hμ, l, hl0, hle⟩ := UpperTheory.V.Hi.OrdB.exists_form (isSmooth_jacB hπ) hl hx0
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = μ := by
    refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hμs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩
    rw [torusChar_apply]
    conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  have hsq : IsSubquotient π (prinSeries ψ) := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle
  have hψφ : ∀ i (u : Uo k), ψ i u = (φ (eT k n i u))⁻¹ := fun i u => by
    have hO : (Pi.mulSingle i (u : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n) := fun j => by
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]; exact u.2
      · simp [Pi.mulSingle_eq_of_ne h]
    have h1 : jacB π (Pi.mulSingle i (u : kˣ)) (p v) = (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ) • p v := by
      rw [hp, UnramFixed.deltaHalf_torusO k hO, inv_one, Units.val_one, one_smul, ← map_smul]
      exact congrArg p (hv.2.2 (eT k n i u))
    rw [← UpperTheory.V.Hi.OrdB.tc_single]
    exact Units.ext (hμ _ _ h1)
  obtain ⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ :=
    ⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩
  have hω : ∀ i, IsSmoothChar (ω i) := fun i => by
    have := (hψ i).mul (isSmoothChar_of_isUnram (isUnram_absPow k (-(((n : ℂ) - 1) / 2))))
    rwa [absPow_neg, mul_inv_cancel_right] at this
  have hinv : IsInvOn φ ω := fun i u => by
    have := hψφ i u
    rw [MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one] at this
    rw [this, inv_inv]
  refine ⟨ω, hω, hinv, hsq, fun j => ?_⟩
  have hm : (j : ℕ) + 1 ≤ n := j.2
  have h1 := propCp _ (glIwa k n) ℂ V π _ (al_mem k n ((j : ℕ) + 1)) v hv.1
  rw [hker, hidx _ hm] at h1
  have h2 : p _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
  rw [map_sub, map_smul, sub_eq_zero, (ha j).2, map_smul] at h2
  have hQ : ((Nat.card 𝓀[k] ^ (((j : ℕ) + 1) * (n - ((j : ℕ) + 1))) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ Nat.card_pos.ne')
  have h3 := hμ (fun i => UpperTheory.V.Hi.unif k ^ (if (i : ℕ) < (j : ℕ) + 1 then 1 else 0 : ℤ))
    ((((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n)
      (fun i => UpperTheory.V.Hi.unif k ^ (if (i : ℕ) < (j : ℕ) + 1 then 1 else 0 : ℤ))))⁻¹ : ℂˣ) : ℂ) *
      (((Nat.card 𝓀[k] ^ (((j : ℕ) + 1) * (n - ((j : ℕ) + 1))) : ℕ) : ℂ)⁻¹ * a ((j : ℕ) + 1))) (by
    rw [hp, mul_smul]
    congr 1
    rw [mul_smul, h2, smul_smul, inv_mul_cancel₀ hQ, one_smul]
    rfl)
  have key : ∀ (Q x : ℂ) (d : ℂˣ), Q ≠ 0 → Q * ((d : ℂ) * (((d⁻¹ : ℂˣ) : ℂ) * (Q⁻¹ * x))) = x := fun Q x d h => by
    rw [Units.val_inv_eq_inv_val]
    have := d.ne_zero
    field_simp
  rw [← UpperTheory.V.Hi.OrdB.num ω hm, h3]
  exact key _ _ _ hQ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PartPt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private cl_one cl_mem classical_fixed_by_iwahori cl_gen cl_stab cl_Yuz from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClParts
open private pa_fin pa_part from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0

namespace UpperTheory.V.Z.Ord

private theorem ord_parts {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A]
    (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ) {P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.Part ι lam ξ → Prop}
    (hP : AutY H ι P) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d) (hs : H.IsSpec θ ι x.toRingHom lam ξ c0 sp) (hlam : lam ∈ H.admitted) (K : H.Lev) :
    H.OrdAt θ ι x.toRingHom lam ξ K c0 =
      ⨆ Y : {Y : H.Part ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K c0 := by
  have h1 : H.ClAt θ ι x.toRingHom lam ξ K c0 ≤
      ⨆ Y : {Y : H.Part ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    intro F hF
    have hF' := (cl_mem H ι θ _ lam ξ K c0 F).1 hF
    exact cl_one H ι θ _ lam ξ K c0 hH (fun Y : {Y : H.Part ι lam ξ // P lam d ξ Y} => Y.1) F hF
      (hP lam hlam d ξ hs.alg F hF'.1 ⟨K, hF'.2.1⟩ ⟨c0, classical_fixed_by_iwahori H ι θ _ lam ξ K c0 c0 le_rfl hs.triv F hF⟩)
  refine le_antisymm (iSup_le fun μ => ?_) (iSup_le fun _ => inf_le_right)
  haveI := hs.fin K c0 le_rfl
  have h2 := cl_gen (fun Y : {Y : H.Part ι lam ξ // P lam d ξ Y} => Y.1.Y) (H.ClAt θ ι x.toRingHom lam ξ K c0) (H.uzC ι lam d)
    (cl_stab H ι θ _ lam ξ K c0 c0 le_rfl hs.triv) (fun Y => cl_Yuz H ι lam ξ Y.1) h1 μ.1
  have h3 : H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1 ≤ H.OrdAt θ ι x.toRingHom lam ξ K c0 :=
    le_iSup (fun μ : {μ : ℂ // ‖ι.symm μ‖ = 1} =>
      H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1) μ
  exact h2.trans (iSup_mono fun Y => inf_le_inf_left _ h3)

set_option maxHeartbeats 800000 in
theorem partPt : GlobalTheory.Mem.LiteralAutomorphy.LitN → PartPt := by
  intro _ L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ y hy
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := IsCNL.finite
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨h0, hfin, hfree, hK⟩ := hiComm L Ω l n c H hH A θ hθ K
  haveI := (hK a).2.1
  obtain ⟨e, he, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) h0
  obtain ⟨-, -, -, -, -, -, h4, -⟩ := pa_fin (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A)
    e he hi hY ι x sp (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K)
    _ (Submodule.span ℂ (sp '' H.MK θ a K)) (hsp.span K c0 le_rfl) rfl (fun Y : {Y : H.Part ι lam ξ // P lam d ξ Y} => Y.1.Y)
    (fun Y => pa_part H ι lam ξ Y.1) (ord_parts H hH θ ι hP x lam d ξ c0 sp hsp hlam K)
  obtain ⟨Y, F, hF0, hF, h⟩ := h4 y hy
  exact ⟨Y.1, F, Y.2, hF0, hF, h⟩

end UpperTheory.V.Z.Ord
end

