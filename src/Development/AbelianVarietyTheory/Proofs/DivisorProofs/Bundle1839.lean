import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelTensorValues
section
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSpan

theorem exists_form {G Γ W X Y : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [AddCommGroup Y]
    [Module ℂ Y] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (h : G)
    (hfin : Finite (Bridge.stab ι J h)) (w : W) (p : X → G) (Φ : X → W →ₗ[ℂ] Y) (v : Y)
    (law : ∀ x γ (k : J), p x = ι γ * h * k → Φ x (ρ γ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • v) :
    ∃ f ∈ Bridge.AdForms ι ρ J χ, ∃ N : G → ℕ, (∀ x, Φ x (f (p x)) = (N (p x) : ℂ) • v) ∧
      ∀ γ (k : J), N (ι γ * h * k) ≠ 0 := by
  let S : G → Set Γ := fun x => {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}
  have hS : ∀ x, (S x).Finite := by
    intro x
    rcases (S x).eq_empty_or_nonempty with e | ⟨γ₀, h₀⟩
    · rw [e]; exact Set.finite_empty
    · refine (Set.finite_range fun δ : Bridge.stab ι J h => γ₀ * δ.1).subset fun γ hγ => ⟨⟨γ₀⁻¹ * γ, ?_⟩, by simp⟩
      rw [Bridge.mem_stab]
      have := J.mul_mem h₀ (J.inv_mem hγ)
      convert this using 1
      simp only [map_mul, map_inv]
      group
  let term : G → Γ → W := fun x γ =>
    if hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J then ((χ ⟨_, hm⟩ : ℂˣ) : ℂ) • ρ γ w else 0
  have hsupp : ∀ x, Function.support (term x) ⊆ (hS x).toFinset := by
    intro x γ hγ
    by_contra hn
    have : ¬ h⁻¹ * (ι γ)⁻¹ * x ∈ J := fun hm => hn ((hS x).mem_toFinset.2 hm)
    exact hγ (dif_neg this)
  have hterm : ∀ δ x (k : J) γ, term (ι δ * x * k) (δ * γ) = ((χ k : ℂˣ) : ℂ) • ρ δ (term x γ) := by
    intro δ x k γ
    have e : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
      simp only [map_mul]; group
    by_cases hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J
    · have hm' : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := e ▸ J.mul_mem hm k.2
      have e' : (⟨_, hm'⟩ : J) = ⟨_, hm⟩ * k := Subtype.ext e
      simp only [term, dif_pos hm, dif_pos hm']
      rw [e', map_mul χ, map_mul ρ, map_smul, smul_smul, Units.val_mul, mul_comm]
      rfl
    · have hm' : ¬ h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := fun hh =>
        hm ((J.mul_mem_cancel_right k.2).1 (e ▸ hh))
      simp only [term, dif_neg hm, dif_neg hm', map_zero, smul_zero]
  refine ⟨fun x => ∑ᶠ γ, term x γ, ?_, fun x => (hS x).toFinset.card, fun x => ?_, fun γ k => ?_⟩
  · intro δ x k
    show ∑ᶠ γ, term (ι δ * x * k) γ = ((χ k : ℂˣ) : ℂ) • ρ δ (∑ᶠ γ, term x γ)
    rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
    have hf : (Function.support (term x)).Finite := (hS x).toFinset.finite_toSet.subset (hsupp x)
    have := (((χ k : ℂˣ) : ℂ) • ρ δ).toAddMonoidHom.map_finsum hf
    refine Eq.trans ?_ this.symm
    exact finsum_congr fun γ => hterm δ x k γ
  · show Φ x (∑ᶠ γ, term (p x) γ) = _
    rw [finsum_eq_sum_of_support_subset _ (hsupp _), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hm : h⁻¹ * (ι γ)⁻¹ * p x ∈ J := (hS _).mem_toFinset.1 hγ
    simp only [term, dif_pos hm]
    rw [map_smul, law x γ ⟨_, hm⟩ (by simp only []; group), smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  · refine (Finset.card_pos.2 ⟨γ, (hS _).mem_toFinset.2 ?_⟩).ne'
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    convert k.2 using 1
    group

theorem law_abstract {H G' W X : Type} [Group H] [Group G'] [AddCommGroup W] [Module ℂ W]
    (om : H × G' →* Module.End ℂ (X → ℂ)) (ρ : H →* Module.End ℂ W) (L : W →ₗ[ℂ] (X → ℂ))
    (x h γ k a : H) (hu : h⁻¹ * γ⁻¹ * x = k * a) (c : ℂ) (hk : ρ k⁻¹ = 1) (hh : ρ h⁻¹ = 1) (hx : ρ x = 1)
    (hLk : ∀ w, om (k, 1) (L w) = c • L w) (hLa : ∀ w, om (a, 1) (L w) = L (ρ a w)) (w : W) (g : G') :
    om (x, g) (L (ρ γ w)) = om (γ, 1) (c • om (h, g) (L w)) := by
  have e4 : x = γ * h * k * a := by rw [mul_assoc _ k, ← hu]; group
  have e5 : (x, g) = ((γ, 1) : H × G') * ((h, g) * ((k, 1) * (a, 1))) := by
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [e4]; simp only [mul_assoc]
  have e6 : ρ a * ρ γ = 1 := by
    have : a = k⁻¹ * h⁻¹ * γ⁻¹ * x := by rw [e4]; group
    rw [this, map_mul, map_mul, map_mul, hx, hk, hh, one_mul, one_mul, mul_one, ← map_mul, inv_mul_cancel, map_one]
  rw [e5, map_mul om, Module.End.mul_apply, map_mul om, map_mul om, Module.End.mul_apply, Module.End.mul_apply, hLa,
    ← Module.End.mul_apply (ρ a), e6, Module.End.one_apply, hLk, map_smul]

theorem map_quot {H G : Type} [Group H] [Group G] (p : H →* G) (x h γ : H) (k : G) (e : p x = p γ * p h * k) :
    p (h⁻¹ * γ⁻¹ * x) = k := by
  rw [map_mul, map_mul, map_inv, map_inv, e]
  group

theorem kernel_law {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (c : CoefA S) (hc : c.Is) (J : Subgroup (Bridge.Gf S)) (χ : J →* ℂˣ)
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ J, ∀ w, om (k, 1) (Λ w) = ((χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {h x : GA D S} (hh : h ∈ GfC S) (hx : x ∈ GfC S) (γ : GQ S) (k : J)
    (e : fin S x = Bridge.ratF S γ * fin S h * k) (w : c.W) (g : GA D T) :
    thetaKO om x g (Λ (c.ρ γ w)) = ((χ k : ℂˣ) : ℂ)⁻¹ * thetaKO om h g (Λ w) := by
  refine (GlobalTheory.LiftUnfold.exists_fin_mul_real S (h⁻¹ * (γ : GA D S)⁻¹ * x)).elim fun k' hk0 => hk0.2.elim fun a ha0 => ?_
  have hk := hk0.1
  have ha := ha0.1
  have e2 : fin S k' = k := ha0.2.2.trans (map_quot (finHom S).rangeRestrict x h γ k e)
  have hk' : fin S k' ∈ J := by rw [e2]; exact k.2
  have e3 : (⟨fin S k', hk'⟩ : J) = k := Subtype.ext e2
  have h1 : ∀ w, om (k', 1) (Λ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • Λ w := fun w =>
    (hΛk k' hk hk' w).trans (congrArg (fun z : J => ((χ z : ℂˣ) : ℂ)⁻¹ • Λ w) e3)
  have h2 := law_abstract om c.ρ Λ x h γ k' a ha0.2.1 _ (hc.1 _ (inv_mem hk)) (hc.1 _ (inv_mem hh)) (hc.1 _ hx)
    h1 (hΛa a ha) w g
  refine (congrFun h2 0).trans ?_
  have h3 := hom.om_aut γ γ.2 1 (one_mem _) _ (hom.om_pres (h, g) _ (hΛ w))
  refine (congrFun ((om ((γ : GA D S), 1)).map_smul _ _) 0).trans ?_
  exact congrArg (fun z : ℂ => ((χ k : ℂˣ) : ℂ)⁻¹ * z) h3

theorem ne_zero_of_coset {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) (N : G → ℕ) (h y : G)
    (hN : ∀ γ (k : J), N (ι γ * h * k) ≠ 0) (γ : Γ) (u : J) (e : h = ι γ * y * u) : N y ≠ 0 := by
  have := hN γ⁻¹ u⁻¹
  rwa [e, map_inv, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left] at this

theorem coeff_ne_zero {I : Type} [Fintype I] (r : ℕ) (s N : I → ℕ) (hr : r ≠ 0) (hs : ∀ i, s i ≠ 0) (i₀ : I)
    (hN : N i₀ ≠ 0) : ∑ i, (r : ℂ)⁻¹ * (s i : ℂ)⁻¹ * (N i : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < ∑ i, (r : ℝ)⁻¹ * (s i : ℝ)⁻¹ * (N i : ℝ) :=
    Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ _, by have := hs i₀; positivity⟩
  have h' := Complex.ofReal_ne_zero.2 h.ne'
  push_cast at h'
  exact h'

theorem exists_integral {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = (((levEnv S β L).χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : MeasureTheory.Measure (GA D S)} {𝓕 : Set (GA D S)}
    (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (Cl : Type) [Fintype Cl] (y : Cl → GA D S)
    (hy : Bridge.IsReps (Bridge.ratF S) (levEnv S β L).J (fun k => fin S (y k)))
    (hyf : ∀ k, Finite (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k))))
    (hh : ∀ k, y k ∈ GfC S) {h : GA D S} (hf : h ∈ GfC S) (w : c.W) :
    ∃ f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ, ∃ a : ℂ, a ≠ 0 ∧
      ∀ g, ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = a * thetaKO om h g (Λ w) := by
  let Φ : Cl → c.W →ₗ[ℂ] (GA D T → ℂ) := fun k =>
    LinearMap.pi fun g => LinearMap.proj (0 : WO S T) ∘ₗ om (y k, g) ∘ₗ Λ
  have hex := exists_form (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ (fin S h)
    (GlobalTheory.SplitReps.finite_stab_of_reps _ le_rfl hy hyf _) w (fun k => fin S (y k)) Φ
    (fun g => thetaKO om h g (Λ w)) (fun x γ k e => funext fun g =>
      kernel_law hom c hc _ _ Λ hΛ hΛa hΛk hf (hh x) γ k e w g)
  refine hex.elim fun f hf0 => hf0.2.elim fun N hN => ?_
  have hrel : (levEnv S β L).J.relIndex (levEnv S β L).J ≠ 0 := by simp
  have h0 : ∃ k, N (fin S (y k)) ≠ 0 := by
    refine (hy (fin S h)).exists.elim fun k hk => hk.elim fun γ hγ => hγ.elim fun u e => ⟨k, ?_⟩
    exact ne_zero_of_coset (Bridge.ratF S) _ N _ _ hN.2 γ u e
  refine h0.elim fun k₀ hk₀ => ⟨f, hf0.1, _, coeff_ne_zero _
    (fun k => Nat.card (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k)))) (fun k => N (fin S (y k))) hrel
    (fun k => (have := hyf k; Nat.card_pos.ne')) k₀ hk₀, fun g => ?_⟩
  refine (GlobalTheory.LiftUnfold.integral_theta hom hs hp c hc β L hL hf0.1 Λ hΛ hΛa hΛk hν _ Cl y le_rfl hrel hy hh g).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : thetaKO om (y k) g (Λ (f (fin S (y k)))) = (N (fin S (y k)) : ℂ) * thetaKO om h g (Λ w) :=
    congrFun (hN.1 k) g
  rw [h1, ← mul_assoc]

theorem mem_span_of_linear {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (j : I → H)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (T : H →ₗ[ℂ] Y) (y : H) (a : ℂ) (ha : a ≠ 0) (v : Y) (e : T y = a • v) :
    v ∈ Submodule.span ℂ (Set.range fun x => T (j x)) := by
  have h1 : T y ∈ (Submodule.span ℂ (Set.range j)).map T := Submodule.mem_map_of_mem (hj ▸ Submodule.mem_top)
  rw [Submodule.map_span, ← Set.range_comp, e] at h1
  exact (Submodule.smul_mem_iff _ ha).1 h1

theorem span_eq_top_of_model {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (e : H →ₗ[ℂ] Y)
    (he : Function.Injective e) (j : I → H) (x : I → Y) (hj : ∀ i, e (j i) = x i)
    (hx : Submodule.span ℂ (Set.range x) = LinearMap.range e) : Submodule.span ℂ (Set.range j) = ⊤ := by
  refine Submodule.map_injective_of_injective he ?_
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, ← hx]
  exact congrArg (fun z => Submodule.span ℂ (Set.range z)) (funext hj)

end GlobalTheory.KernelSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectors
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaShiftSmooth

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (κ : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  have hs : (flagL (R.datWp i R.triv)).s = 0 := rfl
  have hQ : (flagL (R.datWp i R.triv)).Q = ∅ := rfl
  rw [hs, hQ]
  simp

theorem exists_translate (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) :
    ∃ U ∈ R.Wall i σ, ∀ v x, U v x = X v (x * κ') := by
  refine ⟨postOn (R.MW i σ) (actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0) X,
    GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) g0 X hX _ fun _ => rfl, fun v x => ?_⟩
  have hT : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (X v) := fun k hk h =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i σ) _ _ X hX v).2.2 k hk h
  have h1 := level_action_spec (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) hT ⟨κ', hκ'⟩ κ' hκ' x
  rw [levChi_flag_eq_one, inv_one, one_mul] at h1
  exact h1

theorem translate_of_lowT (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X X' : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) (hX' : X' ∈ R.Wall i σ)
    (h : ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (x : GA D (Wc D i)), X' (fun ρ => v ρ) x = X (fun ρ => v ρ) (x * κ'))
    (v : (R.MW i σ).Vec) (x : GA D (Wc D i)) : X' v x = X v (x * κ') := by
  obtain ⟨U, hU, hUv⟩ := exists_translate R hθ i σ g0 κ' hκ' X hX
  have h0 : X' - U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i σ) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ (X' - U) (Submodule.sub_mem _ hX' hU) fun w => by
      funext z
      exact sub_eq_zero.2 ((h w z).trans (hUv _ z).symm)
  rw [sub_eq_zero.1 h0]
  exact hUv v x

theorem thF_shift_all : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : (R.MW i (sg0 D A)).Vec) (x : GA D (Wc D i)), R.thF i t y' v x = R.thF i t y v (x * κ') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hP i t g0 κ κ' hκ hκ' y y' hy
  exact translate_of_lowT R hM.inf i (sg0 D A) g0 κ' hκ' (R.thF i t y) (R.thF i t y') (hP.thF_mem i t y)
    (hP.thF_mem i t y') (GlobalTheory.T.thetaLift_intertwines_levelLifts_lowestKType R hL hM hP i t g0 κ κ' hκ hκ' y y' hy)

end GlobalTheory.ThetaShiftSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNZOfPolAt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ThetaNormal

theorem thetaNZ_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.admitted R (IsLocalRing.maximalIdeal R) → ∀ (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → GlobalTheory.LN.SplitOver t.G (IsLocalRing.maximalIdeal R) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ hA t hpol hs
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h1 h2 E H R t hpol
  have := hA.1.1
  obtain ⟨P, hPL, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric h1 R A t.G t.semi gen hgen t.PP t.cub t.sym
  have hσ : ∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0 := by
    rw [hPL]; exact GlobalTheory.T.exists_nonzero_section_of_polarised_generic_fibre E H R t hpol
  obtain ⟨D, U, hUL, -⟩ := GlobalTheory.T.semiabelian_generic_fibre_polarization_iso R hA t.G P t.semi (hPL ▸ GlobalTheory.LN.UnifPrime.hypW_of_triple t) hs A gen hgen
    (hPL ▸ hL) hσ
  have key := GlobalTheory.T.exists_section_nonzero_on_closed_fibre_complete_local R hA.1.1 hA.1.2.2.1 hA.2.1 hA.2.2.1 D A t.G t.semi U
  rw [hUL, hPL] at key
  have := t.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint t.G _ key

end GlobalTheory.ThetaNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalDarbouxQuasiInvariantCmStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_rationalDarboux_quasiInvariant_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (Formalism.IndefR.DatumF.ratWF γ + w) =
              B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ w := by
  first | exact @GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi | exact GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi | (intros; apply GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCmUnitaryShimuraMemClosureLinearHomImagesStatement
section
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_cmUnitaryShimura_mem_closure_linearHom_images : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (f : (X.A true).t.G ⟶ X.B.t.G),
        x ^ n = 1 ∧ GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
        (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) ∧
        w = x ≫ f} := by
  first | exact @GlobalTheory.FlatCM.TorsGen.gen | exact GlobalTheory.FlatCM.TorsGen.gen | (intros; apply GlobalTheory.FlatCM.TorsGen.gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualRingOfIntegersIffOfUnramifiedExtension
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped nonZeroDivisors

namespace GlobalTheory.UnrTraceDual

theorem traceDual_ringOfIntegers_iff_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔ ∀ d ∈ differentIdeal ℤ (𝓞 F), IsIntegral ℤ (algebraMap F E (d : F) * e) := by
  intro F E _ _ _ _ _ hU e
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := inferInstance
  have hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]
  have hint : ∀ x : E, IsIntegral ℤ x ↔ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro x
    rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]
  have h1 : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔
      e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    constructor
    · intro h a ha
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 ha
      rw [Algebra.traceForm_apply, mul_comm]
      exact RingHom.mem_range.2 (IsIntegrallyClosed.isIntegral_iff.1 (h o))
    · intro h o
      have := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).2 ⟨o, rfl⟩)
      rw [Algebra.traceForm_apply, mul_comm] at this
      exact IsIntegrallyClosed.isIntegral_iff.2 (RingHom.mem_range.1 this)
  have h2 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  have hne : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [h1, h2, FractionalIdeal.mem_inv_iff hne, hEq]
  let J : Ideal (𝓞 E) :=
    { carrier := {x | IsIntegral ℤ (algebraMap (𝓞 E) E x * e)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add, add_mul] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, zero_mul]
        exact isIntegral_zero
      smul_mem' := by
        intro c x hx
        have hx' : IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := hx
        have hc : IsIntegral ℤ (algebraMap (𝓞 E) E c) := RingOfIntegers.isIntegral_coe c
        show IsIntegral ℤ (algebraMap (𝓞 E) E (c * x) * e)
        rw [map_mul, mul_assoc]
        exact IsIntegral.mul hc hx' }
  have hJ : ∀ x : 𝓞 E, x ∈ J ↔ IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := fun _ => Iff.rfl
  have hL : (∀ y ∈ (((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 E)) :
      FractionalIdeal (𝓞 E)⁰ E), e * y ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔
      (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) ≤ J := by
    constructor
    · intro h x hx
      rw [hJ, hint, mul_comm]
      exact h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hx)
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      rw [mul_comm, ← hint]
      exact (hJ x).1 (h hx)
  rw [hL, Ideal.map_le_iff_le_comap]
  constructor
  · intro h d hd
    have := (hJ _).1 (h hd)
    rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
  · intro h d hd
    show algebraMap (𝓞 F) (𝓞 E) d ∈ J
    rw [hJ, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact h d hd

end GlobalTheory.UnrTraceDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHermitianTensorIntegralOfCharTrivial
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.KFinLoc

theorem symp_incM_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (θ : E) (x y : Matrix (Fin n) (Fin d) E) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) (inclR (F := F) (AF F) θ) (incM F JA) (incM F JB)
      (incM F x) (incM F y) =
      algebraMap F (AF F) (Algebra.trace F E (θ * GlobalTheory.WeilM.hTens σ JA JB x y)) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (AF F ⊗[F] E) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [← ht, GlobalTheory.WeilM.symp]
  simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, hc, map_mul, map_sum]

theorem trace_hTens_integral_of_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F), PsiUnr ψ v →
    ∀ X₀ : Matrix (Fin n) (Fin d) E, (∀ γ ∈ latAtV X Y v,
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1) →
    ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v) (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)))
      ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ ψ n d X Y v hψ X₀ h x hx y hy
  refine (hψ _).1 fun t ht => ?_
  have hat : At (evFin F v) (GlobalTheory.EmbChart.atPlace v t) := fun u hu => by
    rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hmem : GlobalTheory.EmbChart.atPlace v t • incM F (Matrix.vecMulVec x y) ∈ latAtV X Y v :=
    AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v t, hat, by rw [GlobalTheory.EmbChart.evFin_atPlace]; exact ht,
      x, hx, y, hy, rfl⟩
  have h1 := h _ hmem
  have hm : (-1 : AE F E) = inclR (F := F) (AF F) (-1 : E) := by rw [map_neg, map_one]
  rw [GlobalTheory.LatVac.symp_smul_smul, hm, symp_incM_mat, GlobalTheory.EmbChart.atPlace_mul_right,
    GlobalTheory.EmbChart.atPlace_mul_right, GlobalTheory.EmbChart.evFin_atPlace, one_mul, AlgHom.commutes, neg_one_mul,
    mul_comm] at h1
  exact h1

end GlobalTheory.KFinLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariantStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceSymplecticForm_unitaryGroupAction_invariant : ∀ {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB)
    (x y : Matrix α β E), symp c ξ JA JB (actB c g x) (actB c g y) = symp c ξ JA JB x y := by
  first | exact @GlobalTheory.DblVacEigen.SympAct.symp_actB | exact GlobalTheory.DblVacEigen.SympAct.symp_actB | (intros; apply GlobalTheory.DblVacEigen.SympAct.symp_actB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorEqTranslateUnitVectorStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_cosetVector_eq_translate_unitVector : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∃ x : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) ∧ (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) ∧ W.Om r 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) (W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
  first | exact @GlobalTheory.FunObj.StdDatum.LiftCoset.om_cosetV_eq | exact GlobalTheory.FunObj.StdDatum.LiftCoset.om_cosetV_eq | (intros; apply GlobalTheory.FunObj.StdDatum.LiftCoset.om_cosetV_eq <;> assumption)
end

