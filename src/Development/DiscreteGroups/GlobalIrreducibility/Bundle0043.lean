import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZero
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0027
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameUniformizerPower

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.RegularLocalOfDepthZero
section
noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt

theorem le_of_sigmaEquiv {s n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin s) : d a ≤ n := by
  have h1 := Fintype.card_le_of_injective _ (sigma_mk_injective (β := fun a => Fin (d a)) (i := a))
  simpa [Fintype.card_congr e] using h1

section Loc

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory GlobalTheory.RegType

variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {w : HeightOneSpectrum (𝓞 E)}
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) (hDZ : DiscreteGroups.sglob.DzType.DepthZeroInertiaBig)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ

theorem inePol_cusp {n : ℕ} (hn : 0 < n) (hbig : n = 1 ∨ 16 * n ^ 2 < g) (σ : Irr (w.adicCompletion E) n) (hc : IsCuspidal σ.π) (f : (ZMod g)[X])
    (hf : Has (sysOf L h5 hA) (σ.π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) f) :
    (rc (cls σ.toIrrRep)).inePol t = TameGen.liftPoly L.teich f := by
  have hi' := GlobalTheory.TameRecord.continuous_symm w i hi
  have hc' : IsCuspidal (σ.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)) :=
    GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap i.symm hi σ.π hc
  let ρ : GLRep g := ⟨n, Rep.of (σ.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom))⟩
  have hρ : TameGen.IsSC ρ := ⟨hn, (Model.isIrrRep_iff _).2 (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp σ.irr _
      fun y => ⟨_, GlobalTheory.TameRecord.glMap_apply_symm i y⟩), GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal _ _ _ _ hc'⟩
  obtain ⟨τ, φ, hs, hinj, heq, he⟩ := TameGen.exists_simple_of_has (sysOf L h5 hA) ρ.2.ρ f hf
  have hφ : (fixK1 ρ.2.ρ).subtype ∘ₗ φ ≠ 0 := fun e => by
    have h0 : ∀ u : τ, u = 0 := fun u => hinj (Subtype.ext (by simpa using LinearMap.congr_fun e u))
    exact CategoryTheory.id_nonzero τ (by ext u; exact (h0 _).trans (h0 _).symm)
  have hfix : fixK1 ρ.2.ρ ≠ ⊥ := fun e => hφ (LinearMap.ext fun u => (Submodule.eq_bot_iff _).1 e _ (φ u).2)
  have hτ : FiniteGL.IsCuspidal τ.ρ := fun b hb hb' u hu => hinj (by
    rw [map_zero]
    exact GlobalTheory.DepthZeroCusp.depthZeroCuspidal g ρ hρ hfix b hb hb' _ fun x hx => by rw [← heq, hu x hx])
  refine hDZ E Ω g A w h rc hrc i hi κ L t ht hκ n hbig σ.toIrrRep (IrrGL.isCusp_of.2 ⟨hn, hc⟩) τ f
    (isCuspOf_of_series L h5 hA τ (TameGen.isCusp_character hn τ hs hτ) f he) ⟨_, hφ, fun k u => ?_⟩
  exact (congrArg Subtype.val (heq (red g n k) u)).trans (repK_red ρ.2.ρ k (φ u))

theorem inePol_of_has (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma) {n : ℕ}
    (π : Irr (w.adicCompletion E) n) (hB : 16 * n ^ 2 < g) (f : (ZMod g)[X])
    (hf : Has (sysOf L h5 hA) (π.π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) f) :
    (rc (cls π.toIrrRep)).inePol t = TameGen.liftPoly L.teich f := by
  have hi' := GlobalTheory.TameRecord.continuous_symm w i hi
  obtain ⟨s, d, σ, hs⟩ := GlobalTheory.T.exists_cuspidalSupport_irreducibleSmoothGL hBZ hGL _ n π
  have h1 := hrc.recSupp n s π d σ hs (ineIncl h ⟨t, ht⟩)
  obtain ⟨-, hc, e, U, T, hT⟩ := hs
  obtain ⟨φ⟩ := GlobalTheory.IndField.multiProd_comp_glMap i.symm hi' hi
    (GlobalTheory.SplitWeil.nabs_map_of_homeomorph i.symm hi' hi) e (fun a => (σ a).π)
  have h2 : IsSubquotient (π.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom))
      ((multiProd e fun a => (σ a).π).comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)) :=
    ⟨⟨U.toSubmodule, fun x _ hv => U.apply_mem_toSubmodule _ hv⟩, ⟨T.toLinearMap, fun x => T.isIntertwining' _⟩, hT⟩
  obtain ⟨fs, hfs, rfl⟩ := series_of_isSubquotient (sysOf L h5 hA) e
    (fun a => (σ a).π.comp (Matrix.GeneralLinearGroup.map (n := Fin (d a)) i.toRingHom))
    (h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)) f hf
  have hbig : ∀ a, d a = 1 ∨ 16 * d a ^ 2 < g := fun a =>
    Or.inr (lt_of_le_of_lt (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (DiscreteGroups.sglob.DzType.Rt.le_of_sigmaEquiv e a) 2)) hB)
  have h3 : ∀ a, (rc (cls (σ a).toIrrRep)).charPol (ineIncl h ⟨t, ht⟩) = TameGen.liftPoly L.teich (fs a) := fun a => by
    rw [← WD.inePol_of_mem_Ine _ ht]
    exact DiscreteGroups.sglob.DzType.Rt.inePol_cusp i hi hrc hDZ κ L h5 hA ht hκ (hc a).1 (hbig a) (σ a) (hc a).2.2 _ (hfs a)
  have h4 : ∀ u : Finset (Fin s), TameGen.liftPoly L.teich (∏ a ∈ u, fs a) = ∏ a ∈ u, TameGen.liftPoly L.teich (fs a) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp [TameGen.liftPoly_one]
    | insert a u ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, TameGen.liftPoly_mul _ (TameGen.Has.monic (hfs a)).ne_zero
        (monic_prod_of_monic _ _ fun b _ => TameGen.Has.monic (hfs b)).ne_zero, ih]
  rw [WD.inePol_of_mem_Ine _ ht, h4]
  exact h1.trans (Finset.prod_congr rfl fun a _ => h3 a)

end Loc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilDeligne in

theorem regLoc : GlobalTheory.NRows.Hypotheses₂ → DiscreteGroups.sglob.DzType.DepthZeroInertiaBig → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (Γ : GrpSide D), GreenLab Γ → RegLoc hL D := by
  intro hP hDZ hL D Γ hG k v π ρ f hρ hsq ⟨x, hx, hnk⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
  have hrc := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hw := D.naut.plGw_over k v
  have hA := GlobalTheory.RegType.allLab (Γ.O k) (hG k)
  have h5 := GlobalTheory.SerSys.Bridge.five_le D k
  have hx' := GlobalTheory.RegType.mem_principalCongruenceFixed_of_levelOne hw (I.i k v) (I.cont k v) π.π hx
  have hz := GlobalTheory.RegType.actK_ne_of_notKilled hw (I.i k v) (I.cont k v) π.π hx _ hnk
  have he := GlobalTheory.RegType.eSerC_mul_zIdem (Γ.O k) (hG k) ρ hρ.1 f (by rw [← Γ.eSer_def k f]; exact hρ.2)
  have hHas := GlobalTheory.RegType.has_of_actK (GlobalTheory.RegType.sysOf _ h5 hA) _ hx' hz he
  have hine : (rcAt hL D (D.naut.plGw k v) D.R.r π).inePol (D.ntypes.tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod :=
    DiscreteGroups.sglob.DzType.Rt.inePol_of_has (I.i k v) (I.cont k v) hrc hDZ (Γ.kv k v) _ h5 hA (D.ntypes.tg_mem k v)
      (Γ.tg_tame k v) hP.bz hP.geo π (DiscreteGroups.sglob.DzType.sixteen_sq_lt_g D k) f hHas
  refine ⟨WD.noMonodromy_of_inertia_separable_charpoly _ _ _ _ _ _ _ (D.ntypes.tg_mem k v) ?_, ?_⟩
  · rw [hine]
    exact GlobalTheory.GoodRowMono.separable_prod_teich _ (D.ntypes.teichC_inj k) hsq
  · have hSet : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
      .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
        (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
    have htame : (rcAt hL D (D.naut.plGw k v) D.R.r π).tame := by
      obtain ⟨a, ha, ε, -, hl⟩ := hrc
      refine GlobalTheory.SerSys.LabDepth.tame_of_isTameWD ((hl.depth _).1 ?_)
      refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep π.toIrrRep).some.symm ?_
      refine (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => hx u fun a b => ?_, fun h0 => hz ?_⟩
      · have := GlobalTheory.StepData.mem_KOne.1 hu a b
        rwa [Matrix.sub_apply, Matrix.one_apply] at this
      · rw [h0, map_zero]
    have e1 : (Formalism.CyclotomicNorms.rootsBar f).map (fun x => X - C (D.ntypes.teichC k x)) =
        ((Formalism.CyclotomicNorms.rootsBar f).map (D.ntypes.teichC k)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [labAt, WD.lab_eq_iff_of_tame hSet htame, hine, e1, roots_multiset_prod_X_sub_C]
    exact ⟨GlobalTheory.SerSys.TameGen.Has.monic hHas, rfl⟩

set_option maxHeartbeats 1000000 in
theorem regularLocal_of_depthZero : GlobalTheory.NRows.Hypotheses₂ → DiscreteGroups.sglob.DzType.DepthZeroInertiaBig → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (Γ : GrpSide D), GreenLab Γ → RegLoc hL D :=
  DiscreteGroups.sglob.DzType.Rt.regLoc

end DiscreteGroups.sglob.DzType.Rt

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.TameUniformizerPower
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace DiscreteGroups.sglob.DzType.Rt

open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.DepthZeroRankOneLabel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem value_at_gen [IsTotallyComplex E] (H : DiscreteGroups.sglob.DzType.DepthZeroInertiaBig) {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} (hε : IsDeligneEps ε) {rc : IrrGL (w.adicCompletion E) → WD h} (hl : Laws a ha ε rc)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : GlobalTheory.GLq.LabelDatum g) (t : G E Ω) (ht : t ∈ Ine (F := E) A)
    (hT : TameCoupled A κ t L.gen) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ)
    (htm : GlobalTheory.SplitWeil.IsTame μ) (n : ℕ) (hn : n.Coprime g)
    (hgen : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (n : ZMod g) = L.gen 1) (x : (w.adicCompletion E)ˣ)
    (hx : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - (n : w.adicCompletion E)) < 1) :
    μ (a (ineIncl h ⟨t, ht⟩)) = μ x := by
  haveI : IsLocalHom (PadicInt.toZMod (p := g)) := IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _)
  let u₀ : (ZMod g)ˣ := ZMod.unitOfCoprime n hn
  have hu₀ : IsUnit ((n : ℕ) : ℤ_[g]) := isUnit_of_map_unit (PadicInt.toZMod (p := g)) _ (by
    rw [map_natCast]; exact u₀.isUnit)
  obtain ⟨θ, hθ⟩ := exists_red i hi hw μ htm
  obtain ⟨P, hP, e⟩ := GlobalTheory.Published.DepthZeroModel.exists_label L θ u₀ (by rw [ZMod.coe_unitOfCoprime]; exact hgen)
  have h1 := H E Ω g A w h rc ⟨a, ha, ε, hε, hl⟩ i hi κ L t ht hT 1 (Or.inl rfl) (GlobalTheory.SmGL.IrrRep.det (Fin 1) μ hμ)
    (IrrGL.isCusp_ofChar μ hμ) _ P hP (inflates_units i θ μ hμ hθ)
  have h2 : rc (cls (GlobalTheory.SmGL.IrrRep.det (Fin 1) μ hμ)) = _ := hl.one μ hμ
  rw [h2, e, WD.inePol_of_mem_Ine _ ht, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd] at h1
  have h3 := congrArg (fun p => p.coeff 0) h1
  have h4 : μ (a (ineIncl h ⟨t, ht⟩)) = θ u₀ := Units.ext (by simpa using h3)
  have h5 : u₀ = Units.map (PadicInt.toZMod (p := g)).toMonoidHom hu₀.unit := Units.ext (by simp [u₀])
  rw [h4, h5, hθ]

  set y : (w.adicCompletion E)ˣ :=
    Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom hu₀.unit) with hy
  have hyn : (y : w.adicCompletion E) = n := by simp [hy]
  have hyi : valuation (w.adicCompletion E) ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
    have e4 : ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        i (((hu₀.unit⁻¹ : ℤ_[g]ˣ) : ℤ_[g]) : ℚ_[g]) := by
      rw [hy, ← map_inv, ← map_inv]; rfl
    rw [e4]; exact val_int_le i hi _
  have h6 : μ (x * y⁻¹) = 1 := htm _ (by
    have e3 : ((x * y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        ((x : w.adicCompletion E) - n) * ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
      rw [← hyn, sub_mul, Units.mul_inv]; simp
    rw [e3, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hyi)
  rw [map_mul, map_inv, mul_inv_eq_one] at h6
  exact h6.symm

open GlobalTheory.WeilDeligne in

theorem lab_eq_of_tameRep : DiscreteGroups.sglob.DzType.DepthZeroInertiaBig → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → labAt hL D k v (Irr.ofDet 1 μ hμ) = X - C c := by
  intro hDZ hL D Γ k v μ hμ hT u hu hex c hc
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨a, ha, ε, hε, hl⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hSet : GlobalTheory.WeilDeligne.TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k)
      (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have e1 : rcAt hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 μ hμ) =
      GlobalTheory.WeilDeligne.WD.lpOfChar _ (μ.comp a) (ha.smooth hμ) := hl.one μ hμ
  have hwild : ∀ σ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 (D.naut.plGw k v)),
      (σ : G D.host.E D.nd.Om) ∈ GlobalTheory.WeilDeligne.Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) → (μ.comp a) σ = 1 :=
    GlobalTheory.DepthZeroRankOneLabel.wild_trivial D k v μ hμ hT a ha ε _ hl
  have hval : μ (a ⟨D.ntypes.tg k v, GlobalTheory.WeilDeligne.Ine_le_Weil _ hSet.2.1⟩) =
      μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) := by
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hw := D.naut.plGw_over k v
    have hN := GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw
    have hw2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal ^ 2 := fun h2 => by
      have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast (D.host.g_prime k).ne_zero
      have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
        (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
      have := hs (D.naut.plGw k v).asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h2)
      exact (D.naut.plGw k v).isPrime.ne_top (Ideal.isUnit_iff.1 this)
    obtain ⟨ϖ, π, hϖ, hϖ2, hπ, hv⟩ := hex
    obtain ⟨n, hn, hun, hgen⟩ := GlobalTheory.DepthZeroRankOneLabel.residue_of_cong _ _ _ (D.nd.plOm.2 _) hN hw hw2
      (Γ.kv k v) _ (Γ.ζ k) (D.ntypes.tg_mem k v) (Γ.ζ_gen k) (Γ.tg_tame k v) u ϖ π hϖ hϖ2 hπ hv
    have hx := GlobalTheory.DepthZeroRankOneLabel.val_lt_of_mem hun
    exact DiscreteGroups.sglob.DzType.Rt.value_at_gen hDZ hε hl (I.i k v) (I.cont k v) hw (Γ.kv k v)
      (GlobalTheory.DepthZeroRankOneLabel.labDatum (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k))
      _ (D.ntypes.tg_mem k v) (Γ.tg_tame k v) μ hμ hT n hn hgen _ (by simpa using hx)
  unfold labAt
  rw [e1, GlobalTheory.WeilDeligne.WD.lab_lpOfChar_eq_iff hSet _ hwild c, hc, MonoidHom.comp_apply, hval]

set_option maxHeartbeats 1000000 in
theorem tame_uniformizer_power : DiscreteGroups.sglob.DzType.DepthZeroInertiaBig → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → labAt hL D k v (Irr.ofDet 1 μ hμ) = X - C c :=
  DiscreteGroups.sglob.DzType.Rt.lab_eq_of_tameRep

end DiscreteGroups.sglob.DzType.Rt
end

