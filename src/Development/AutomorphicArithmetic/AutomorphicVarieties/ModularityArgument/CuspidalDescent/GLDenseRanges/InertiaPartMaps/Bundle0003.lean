import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.ZeroDimMemIwahoriFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.EigBoxL
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.CmpOverL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0.InertiaSectionNorm

private theorem Kc_conj {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {g x : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (hx : x ∈ Kc k n 1) : g⁻¹ * x * g ∈ Kc k n 1 := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨a⁻¹ * b * a, ?_, by simp only [map_mul, map_inv]⟩
  have hb' := MonoidHom.mem_ker.1 hb
  exact MonoidHom.mem_ker.2 (by simp only [map_mul, map_inv, hb', mul_one, inv_mul_cancel])

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

private theorem ext_cmp {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have e := h w.1
  rwa [cmp_of w.2, cmp_of w.2] at e

private theorem comm_of {a b : Ga l L n} (h : ∀ w, cmp n w a = 1 ∨ cmp n w b = 1) : Commute a b := by
  refine ext_cmp fun w => ?_
  rw [map_mul, map_mul]
  rcases h w with h | h <;> rw [h] <;> simp

variable (s : HidaSetting l L Ω)

private theorem sec_one (w w' : Plc L) (h : GLw n w) (hw : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n w' (sec n s w h : Ga l L n) = 1 := by
  unfold CaseU.sec
  split_ifs with hb
  · have hm := ((MulEquiv.ofBijective _ hb).symm h).2
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hm w') hw)
  · exact map_one _

private theorem secS_spec (h : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (g : GS n s) :
    toGS n s (secS n s g) = g ∧ secS n s g ∈ GaS n s := by
  unfold secS
  rw [dif_pos h]
  exact ⟨(MulEquiv.ofBijective _ h).apply_symm_apply g, ((MulEquiv.ofBijective _ h).symm g).2⟩

private theorem mem_GaS {x : Ga l L n} (hx : x ∈ GaS n s) {w : Plc L}
    (hw : w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0) : cmp n w x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx w) hw)

private theorem notS {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) :
    w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 :=
  ⟨fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr e))⟩

end UpperTheory.V.Z.Desc.V0.InertiaSectionNorm

open UpperTheory.V.Z.Desc.V0.InertiaSectionNorm in
theorem UpperTheory.V.Z.Desc.V0.normS :
    NormS := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV Q c m τ₀
  obtain ⟨hb, hcomm, hdesc⟩ := secSp l L Ω s n hn V hV
  have spec := secS_spec (n := n) s hb
  have hq : IsEmpty Q.Q := ⟨fun q => Q.notS q (by
    have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
      rw [Q.range]
      exact Or.inr ⟨q, rfl⟩
    rwa [hV] at h)⟩
  have hlev : ∀ K, (hset Q τ₀).lev K = (hset Q τ₀).UQ := fun K => by
    haveI : IsEmpty (hset Q τ₀).Q := hq
    unfold HSet.lev
    rw [iSup_of_empty]
    exact sup_bot_eq _
  have h0 : ∀ (g : GLw n (s.w s.v0)) (t : s.St), cmp n (s.w t) (sec0 n s g) = 1 := fun g t =>
    congrFun (congrArg Prod.fst (spec (1, g)).1) t
  have hτ : ∀ (u u' : Ub n s), (∀ t : s.St, cmp n (s.w t) (u : Ga l L n) = cmp n (s.w t) (u' : Ga l L n)) →
      (hset Q τ₀).τ u = (hset Q τ₀).τ u' := fun u u' h =>
    congrArg τ₀ (Subtype.ext (funext h))
  have huq : ∀ g : GLw n (s.w s.v0), g ∈ KO _ (Fin n) → ∀ u ∈ UQ n Q, ∃ u' ∈ UQ n Q,
      (u' : Ga l L n) = (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g ∧ (hset Q τ₀).τ u' = (hset Q τ₀).τ u := by
    intro g hg u hu
    obtain ⟨k, hk, p, hp, e⟩ := (hdesc Q (u : Ga l L n)).1 ⟨u, hu, rfl⟩
    have hp' : ((p.1, g⁻¹ * p.2 * g) : GS n s) ∈ (KT n (wt s)).prod (Kc _ n 1) :=
      Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 hp).1, Kc_conj hg (Subgroup.mem_prod.1 hp).2⟩
    have hconj : ((p.1, g⁻¹ * p.2 * g) : GS n s) = ((1, g) : GS n s)⁻¹ * p * (1, g) :=
      Prod.ext (by simp) (by simp)
    have e' : (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g = secS n s (p.1, g⁻¹ * p.2 * g) * k := by
      have hc : k * sec0 n s g = sec0 n s g * k := (hcomm (1, g) k hk).eq.symm
      rw [hconj, map_mul, map_mul, map_inv, e]
      change (sec0 n s g)⁻¹ * (secS n s p * k) * sec0 n s g = (sec0 n s g)⁻¹ * secS n s p * sec0 n s g * k
      simp only [mul_assoc, hc]
    obtain ⟨u', hu', e''⟩ := (hdesc Q _).2 ⟨k, hk, _, hp', e'⟩
    have e3 : (u' : Ga l L n) = (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g := e''
    refine ⟨u', hu', e3, hτ _ _ fun t => ?_⟩
    rw [e3, map_mul, map_mul, map_inv, h0, inv_one, one_mul, mul_one]
  refine ⟨fun g hg => ⟨fun K u hu => ?_, fun u hu => huq g hg u hu, fun w hw h => ?_⟩, fun g hg => ?_⟩
  · rw [hlev] at hu
    obtain ⟨u', hu', h⟩ := huq g hg u hu
    exact ⟨u', by rw [hlev]; exact hu', h⟩
  · refine comm_of fun w' => ?_
    by_cases hu : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · refine Or.inl (mem_GaS s (spec (1, g)).2 (notS s ?_))
      rw [hu, ← hV]
      exact hw.1
    · exact Or.inr (sec_one s w w' h hu)
  · obtain ⟨u, hu, e⟩ := (hdesc Q (sec0 n s g)).2 ⟨1, one_mem _, (1, g),
      Subgroup.mem_prod.2 ⟨one_mem _, hg⟩, (mul_one _).symm⟩
    have e3 : (u : Ga l L n) = sec0 n s g := e
    refine ⟨u, hu, e3, ?_⟩
    exact (hτ u 1 fun t => by rw [e3, h0]; exact (map_one _).symm).trans (map_one (hset Q τ₀).τ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.EPartPi
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

open private vs_ne part_eq rank_of from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.ZeroDimMemIwahoriFixed

namespace UpperTheory.V.Z.Desc.V0

section Comp

variable {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] {m : ℕ}
  {ρ : Representation ℂ G M} {ρF : Representation ℂ G (Fin m → M)}

private theorem opE_pi (h : ∀ g F i, ρF g F i = ρ g (F i)) (a : G →₀ ℤ) (F : Fin m → M) (i : Fin m) :
    opE ρF a F i = opE ρ a (F i) := by
  simp only [opE, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, h]

private theorem ePart_pi (h : ∀ g F i, ρF g F i = ρ g (F i)) (a : G →₀ ℤ) (N : ℕ) (F : Fin m → M) :
    F ∈ ePart ρF a N ↔ ∀ i, F i ∈ ePart ρ a N := by
  have hn : ∀ (i : Fin m), ((N : Module.End ℂ (Fin m → M)) F) i = (N : Module.End ℂ M) (F i) := fun i => by
    simp [Module.End.natCast_apply]
  simp only [ePart, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  constructor
  · intro e i
    rw [← opE_pi h, e, hn]
  · intro e
    funext i
    rw [opE_pi h, e i, hn]

end Comp

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {n : ℕ} {s : HidaSetting l L Ω} {V : s.Lev} {lam : Wt L l n} {d : ℕ}

private theorem eC_eq (Q : QData V) {c : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) :
    eC Q τ₀ d a N = Submodule.pi Set.univ fun _ =>
      ePart (((actS n V d).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)) a N := by
  ext F
  refine Iff.trans (ePart_pi (m := m) (M := Ga l L n × GL' n V → Fin d → ℂ) (ρF := (trF (hset Q τ₀) d).comp (sec0 n s))
    (ρ := ((actS n V d).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)) (fun g F i => rfl) a N F) ?_
  exact ⟨fun h i _ => h i, fun h i => h i trivial⟩

private theorem part_eqE (hS : SecS) (hn : 1 ≤ n) (hV : V.S' = s.S) (Q : QData V) {c : Coef l} (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ : Submodule ℂ (UA L n → ℂ))
    (R : Submodule ℂ (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ)) (hR : R = VS V ι e ξ Q τ₀ σ) (b : ℕ)
    (φ : ∀ v : V.frame.Vl, Fin n → Uo ((s.w v.1).adicCompletion L) → ℂ) (μ : V.frame.Vl → Fin n → ℂ)
    (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) :
    YOf Q ι τ₀ e ξ σ ⊓ eigL (fun v : V.frame.Vl => s.w v.1) ((hset Q τ₀).X.rpF ℂ d m) b φ μ ⊓ eC Q τ₀ d a N =
      invE (KT n (wt s)) (Kc _ n 1) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀)
        ((actS n V d).comp (MonoidHom.inr _ _)) a N ⊓ Submodule.pi Set.univ fun _ =>
        R ⊓ eigL (fun v : V.frame.Vl => s.w v.1) ((actS n V d).comp (MonoidHom.inl _ _)) b φ μ := by
  rw [part_eq hS hn hV Q ι τ₀ e ξ σ R hR b φ μ, eC_eq, invE]
  exact inf_right_comm _ _ _

end U

end UpperTheory.V.Z.Desc.V0

set_option maxHeartbeats 1600000 in
open UpperTheory.V.Z.Desc.V0 in
theorem UpperTheory.V.Z.Desc.V0.yDimE :
    UpperTheory.V.Z.J.D.Flath → EigBoxE → UpperTheory.V.Z.J.D.SecS → YDimE := by
  intro hFl hEB hS l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hb σ hσ hun hwt C b φ μ a N
  have hne := vs_ne hn hV Q ι τ₀ e ξ hb hσ hun hwt
  have h0 := hFl l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hb σ hσ hne C
  refine Exists.elim h0 fun f hf => ?_
  have h1 := part_eqE hS hn hV Q ι τ₀ e ξ σ _ hf.2.1 b φ μ a N
  have h2 := hEB L n V.frame.Vl (fun v => s.w v.1) _ _ _ _ _ C.repL C.repS (actS n V d) f hf.1 hf.2.2 m (KT n (wt s)) (Kc _ n 1)
    ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) b φ μ a N
  exact rank_of h1 h2
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.EigBoxE
section
open UpperTheory.V.Z.Desc.V0

theorem UpperTheory.V.Z.Desc.V0.eigBoxE :
    EigBoxE := by
  intro L _ _ n V _ S G H W W' X _ _ _ _ _ _ _ _ ρ κ π f hf hint m K₁ K₂ τ₀ b φ μ a N
  exact eigBoxL ρ κ π f hf hint m K₁ K₂ τ₀ b φ μ a N
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.InvBox
section
noncomputable section

open UpperTheory.V.Hi UpperTheory.V.Z.J.D
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0

section Lin

variable {W Z : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]

private def sl (l : Z →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] W :=
  (TensorProduct.rid ℂ W).toLinearMap ∘ₗ LinearMap.lTensor W l

private def sr (l : W →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] Z :=
  (TensorProduct.lid ℂ Z).toLinearMap ∘ₗ LinearMap.rTensor Z l

private theorem sl_tmul (l : Z →ₗ[ℂ] ℂ) (w : W) (z : Z) : sl l (w ⊗ₜ[ℂ] z) = l z • w := by
  simp [sl]

private theorem sr_tmul (l : W →ₗ[ℂ] ℂ) (w : W) (z : Z) : sr l (w ⊗ₜ[ℂ] z) = l w • z := by
  simp [sr]

end Lin

section Box

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Box

private theorem sl_rTensor_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (l : B →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] A) (x : A ⊗[ℂ] B) : sl l (LinearMap.rTensor B T x) = T (sl l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u v => rw [LinearMap.rTensor_tmul, sl_tmul, sl_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem sr_lTensor_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (l : A →ₗ[ℂ] ℂ) (T : B →ₗ[ℂ] B) (x : A ⊗[ℂ] B) : sr l (LinearMap.lTensor A T x) = T (sr l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u v => rw [LinearMap.lTensor_tmul, sr_tmul, sr_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem mem_range_rTensor_subtype_of_forall_sl_coord_mem {A B ι : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (𝒞 : Module.Basis ι ℂ B) (U : Submodule ℂ A) (x : A ⊗[ℂ] B) (h : ∀ i, sl (𝒞.coord i) x ∈ U) :
    x ∈ LinearMap.range (LinearMap.rTensor B U.subtype) := by
  classical
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right 𝒞 x
  have hc : ∀ i, c i ∈ U := by
    intro i
    have e1 : (TensorProduct.equivFinsuppOfBasisRight 𝒞) (c.sum fun i m => m ⊗ₜ[ℂ] 𝒞 i) = c := by
      rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.apply_symm_apply]
    have e2 := TensorProduct.equivFinsuppOfBasisRight_apply 𝒞 (c.sum fun i m => m ⊗ₜ[ℂ] 𝒞 i) i
    rw [e1] at e2
    rw [e2]
    exact h i
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ⟨⟨c i, hc i⟩ ⊗ₜ 𝒞 i, ?_⟩
  rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]

private theorem memL_lemma_4 {A B ι : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ℬ : Module.Basis ι ℂ A) (V : Submodule ℂ B) (x : A ⊗[ℂ] B) (h : ∀ i, sr (ℬ.coord i) x ∈ V) :
    x ∈ LinearMap.range (LinearMap.lTensor A V.subtype) := by
  classical
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left ℬ x
  have hc : ∀ i, c i ∈ V := by
    intro i
    have e1 : (TensorProduct.equivFinsuppOfBasisLeft ℬ) (c.sum fun i n => ℬ i ⊗ₜ[ℂ] n) = c := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.apply_symm_apply]
    have e2 := TensorProduct.equivFinsuppOfBasisLeft_apply ℬ (c.sum fun i n => ℬ i ⊗ₜ[ℂ] n) i
    rw [e1] at e2
    rw [e2]
    exact h i
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ⟨ℬ i ⊗ₜ ⟨c i, hc i⟩, ?_⟩
  rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]

private theorem box_inl_apply_eq_rTensor {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (g : G)
    (y : W ⊗[ℂ] W') : box ρ κ (g, 1) y = LinearMap.rTensor W' (ρ g) y := by
  simp only [box, Representation.tprod_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one]
  rfl

private theorem box_inr_apply_eq_lTensor {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (h : H)
    (y : W ⊗[ℂ] W') : box ρ κ (1, h) y = LinearMap.lTensor W (κ h) y := by
  simp only [box, Representation.tprod_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one]
  rfl

private theorem opE_box_comp_inr_tmul {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (a : H →₀ ℤ)
    (w : W) (y : W') : opE ((box ρ κ).comp (MonoidHom.inr G H)) a (w ⊗ₜ y) = w ⊗ₜ opE κ a y := by
  simp only [opE, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, MonoidHom.comp_apply,
    MonoidHom.inr_apply, box, Representation.tprod_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one,
    TensorProduct.map_tmul, Module.End.one_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

private theorem mem_box_inr_eigenspace_iff_lTensor_opE_sub_eq_zero {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (a : H →₀ ℤ)
    (N : ℕ) (y : W ⊗[ℂ] W') :
    y ∈ ePart ((box ρ κ).comp (MonoidHom.inr G H)) a N ↔ LinearMap.lTensor W (opE κ a - (N : Module.End ℂ W')) y = 0 := by
  have e : opE ((box ρ κ).comp (MonoidHom.inr G H)) a - (N : Module.End ℂ (W ⊗[ℂ] W')) =
      LinearMap.lTensor W (opE κ a - (N : Module.End ℂ W')) := by
    apply TensorProduct.ext'
    intro w v
    simp [opE_box_comp_inr_tmul, TensorProduct.tmul_sub, Module.End.natCast_apply, TensorProduct.tmul_smul]
  unfold ePart
  rw [LinearMap.mem_ker, e]

private theorem mem_invT_iff_sum_smul_inl_eq_and_inr_fixed {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] {m : ℕ}
    (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ) (ρ : Representation ℂ (G × H) W)
    (F : Fin m → W) :
    F ∈ invT K₁ K₂ τ₀ ρ ↔ (∀ (k : K₁) (i : Fin m), ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • ρ (↑k, 1) (F j) = F i) ∧
      ∀ k ∈ K₂, ∀ i, ρ (1, k) (F i) = F i := Iff.rfl

set_option maxHeartbeats 800000 in
theorem invBox : InvBox := by
  intro G H W W' _ _ _ _ _ _ ρ κ m K₁ K₂ τ₀ a N
  classical
  let Ψ := TensorProduct.piLeft ℂ W' (fun _ : Fin m => W)
  let T : K₁ → Module.End ℂ (Fin m → W) := fun k =>
    LinearMap.pi fun i => ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • (ρ k ∘ₗ LinearMap.proj j)
  have hT : ∀ k (F : Fin m → W) i, T k F i = ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • ρ k (F j) := by
    intro k F i
    simp only [T, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
  haveI indexFFirst : Module.Free ℂ (Fin m → W) := Module.Free.of_divisionRing ℂ _
  haveI indexFSecond : Module.Free ℂ ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W') := Module.Free.of_divisionRing ℂ _
  haveI indexFThird : Module.Free ℂ ↥(inv1 K₁ τ₀ ρ) := Module.Free.of_divisionRing ℂ _
  haveI iL1 : Module.Flat ℂ (Fin m → W) := Module.Flat.of_free
  haveI iL2 : Module.Flat ℂ ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W') := Module.Flat.of_free
  have hV1 : ∀ F : Fin m → W, F ∈ inv1 K₁ τ₀ ρ ↔ ∀ k, T k F = F := by
    intro F
    rw [show inv1 K₁ τ₀ ρ = invT K₁ ⊥ τ₀ (ρ.comp (MonoidHom.fst G Unit)) from rfl, mem_invT_iff_sum_smul_inl_eq_and_inr_fixed]
    simp only [MonoidHom.comp_apply, MonoidHom.coe_fst, map_one, Module.End.one_apply, implies_true, and_true,
      funext_iff, hT]
  have hV2 : ∀ w : W', w ∈ fixd κ K₂ ⊓ ePart κ a N ↔ (∀ l ∈ K₂, κ l w = w) ∧ (opE κ a - (N : Module.End ℂ W')) w = 0 := by
    intro w
    rw [Submodule.mem_inf]
    exact Iff.rfl
  have hΨt : ∀ (F : Fin m → W) (w : W') i, Ψ (F ⊗ₜ w) i = F i ⊗ₜ w := by
    intro F w i
    simp [Ψ]
  have hΨl : ∀ (g : W' →ₗ[ℂ] W') x i, Ψ (LinearMap.lTensor _ g x) i = LinearMap.lTensor W g (Ψ x i) := by
    intro g x i
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]
    | tmul F w => rw [LinearMap.lTensor_tmul, hΨt, hΨt, LinearMap.lTensor_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hΨr : ∀ k x i, Ψ (LinearMap.rTensor W' (T k) x) i =
      ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • LinearMap.rTensor W' (ρ k) (Ψ x j) := by
    intro k x i
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply, smul_zero, Finset.sum_const_zero]
    | tmul F w =>
      simp only [LinearMap.rTensor_tmul, hΨt, hT, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]
  let ι : ↥(inv1 K₁ τ₀ ρ) ⊗[ℂ] ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W') →ₗ[ℂ] (Fin m → W ⊗[ℂ] W') :=
    Ψ.toLinearMap ∘ₗ TensorProduct.map (inv1 K₁ τ₀ ρ).subtype (fixd κ K₂ ⊓ ePart κ a N).subtype
  have hinj : Function.Injective ι :=
    Ψ.injective.comp (TensorProduct.map_injective_of_flat_flat (inv1 K₁ τ₀ ρ).subtype
      (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W').subtype (Submodule.injective_subtype _) (Submodule.injective_subtype _))
  have hrange : invE K₁ K₂ τ₀ (box ρ κ) a N = LinearMap.range ι := by
    apply le_antisymm
    · intro F hF
      obtain ⟨x, rfl⟩ := Ψ.surjective F
      unfold invE at hF
      rw [Submodule.mem_inf, mem_invT_iff_sum_smul_inl_eq_and_inr_fixed, Submodule.mem_pi] at hF
      obtain ⟨⟨h1, h2⟩, h3⟩ := hF
      have hl : ∀ l ∈ K₂, LinearMap.lTensor _ (κ l) x = x := by
        intro l hl
        apply Ψ.injective
        funext i
        rw [hΨl, ← box_inr_apply_eq_lTensor ρ κ l, h2 l hl i]
      have he : LinearMap.lTensor _ (opE κ a - (N : Module.End ℂ W')) x = 0 := by
        apply Ψ.injective
        funext i
        rw [hΨl, map_zero, Pi.zero_apply, ← mem_box_inr_eigenspace_iff_lTensor_opE_sub_eq_zero ρ κ a N]
        exact h3 i (Set.mem_univ i)
      obtain ⟨y, hy⟩ := memL_lemma_4 (Module.Basis.ofVectorSpace ℂ (Fin m → W)) (fixd κ K₂ ⊓ ePart κ a N) x (fun i => by
        rw [hV2]
        refine ⟨fun l hl' => ?_, ?_⟩
        · rw [← sr_lTensor_apply, hl l hl']
        · rw [← sr_lTensor_apply, he, map_zero])
      have hk : ∀ k, LinearMap.rTensor _ (T k) y = y := by
        intro k
        apply Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W'))
        have e := LinearMap.congr_fun ((LinearMap.lTensor_comp_rTensor (f := T k) (g := (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W').subtype)).trans
          (LinearMap.rTensor_comp_lTensor (f := T k) (g := (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W').subtype)).symm) y
        simp only [LinearMap.comp_apply] at e
        rw [e, hy]
        apply Ψ.injective
        funext i
        rw [hΨr]
        refine (Finset.sum_congr rfl fun j _ => ?_).trans (h1 k i)
        rw [box_inl_apply_eq_rTensor]
      obtain ⟨z, hz⟩ := mem_range_rTensor_subtype_of_forall_sl_coord_mem (Module.Basis.ofVectorSpace ℂ ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W')) (inv1 K₁ τ₀ ρ) y (fun i => by
        rw [hV1]
        intro k
        rw [← sl_rTensor_apply, hk k])
      refine ⟨z, ?_⟩
      rw [← hy, ← hz]
      simp only [ι, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | add s t hs ht => rw [map_add]; exact add_mem hs ht
      | tmul v w =>
        have hv := (hV1 v).1 v.2
        obtain ⟨hw1, hw2⟩ := (hV2 w).1 w.2
        have e : ι (v ⊗ₜ w) = fun i => (v : Fin m → W) i ⊗ₜ (w : W') := by
          funext i
          simp only [ι, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul, Submodule.subtype_apply, hΨt]
        rw [e]
        unfold invE
        rw [Submodule.mem_inf, mem_invT_iff_sum_smul_inl_eq_and_inr_fixed, Submodule.mem_pi]
        refine ⟨⟨fun k i => ?_, fun l hl i => ?_⟩, fun i _ => ?_⟩
        · simp only [box_inl_apply_eq_rTensor, LinearMap.rTensor_tmul]
          conv_rhs => rw [← hv k, hT, TensorProduct.sum_tmul]
          simp only [TensorProduct.smul_tmul']
        · rw [box_inr_apply_eq_lTensor, LinearMap.lTensor_tmul, hw1 l hl]
        · rw [mem_box_inr_eigenspace_iff_lTensor_opE_sub_eq_zero, LinearMap.lTensor_tmul, hw2, TensorProduct.tmul_zero]
  rw [hrange, rank_range_of_injective ι hinj, rank_tensorProduct']

end UpperTheory.V.Z.Desc.V0
end
end

