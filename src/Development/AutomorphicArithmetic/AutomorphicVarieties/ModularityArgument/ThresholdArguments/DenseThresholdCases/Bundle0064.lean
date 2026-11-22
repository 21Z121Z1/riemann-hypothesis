import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0050
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0061
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0060
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.ResidualCharpolyRankFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0033
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VSAdIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0034
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0052
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0015

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ProjectedFormsLinkOfPrintedHida
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
open private ev_offL unram_ev ss_irr irr_conj iso_deg_one from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SpehInfLenOne
open private au_isTeich au_open from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
open private split_l from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.FiniteOverL
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
private theorem part2 (H : _root_.UpperTheory.V.Af.HypothesesH') {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {ι : Qbar l ≃+* ℂ}
    {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (hρ : Continuous ρ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    (hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ) (hi : Af.IsIrr (ρ.comp V.pr)) :
    ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (ρ.comp V.pr) π ∧
      (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        π.IsLocComp w τ ↔ IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  have hc : Continuous (ρ.comp V.pr) := hρ.comp (V.pr_cont W.continuous_resP)
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.link2_alt H L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ _ hc hi
    ((ev_offL (K := L) l).mono fun w hw hsp τ hτ B hB => _root_.UpperTheory.Gal.projectedFormsSystemPart.frobLG'_alt H.toClassicalTheorems hc hw hB (hLG w hsp τ hτ))
theorem projected_forms_link_of_printed_hida (H : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ hσ h0
  obtain ⟨Y, hY, -, -, hLG⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt H l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ hσ h0
  refine ⟨Y, hY, fun hi => ?_⟩
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := part2 H s hn Y.cont hσ hLG hi
  exact ⟨π, p1, p2, p3, p4, fun w hw τ => (p5 w hw τ).1⟩
end UpperTheory.Gal.projectedFormsSystemPart
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ResidualCharpolyRankFour
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Win UpperTheory.GalN.V
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
private theorem trace_det_of_charpoly_two {k K : Type} [Field k] [Field K] (ι : k ≃+* K) (g : Matrix (Fin 2) (Fin 2) k) (α β : K)
    (h : g.charpoly.map ι.toRingHom = (X - C α) * (X - C β)) : ι g.trace = α + β ∧ ι g.det = α * β := by
  rw [Matrix.charpoly_fin_two] at h
  have e : (X ^ 2 - C (ι g.trace) * X + C (ι g.det) : K[X]) = (X - C α) * (X - C β) := by
    rw [← h]; simp
  have e1 := congrArg (fun p : K[X] => p.coeff 1) e
  have e0 := congrArg (fun p : K[X] => p.coeff 0) e
  have r : (X - C α) * (X - C β) = (X ^ 2 - C (α + β) * X + C (α * β) : K[X]) := by
    simp only [C_add, C_mul]; ring
  rw [r] at e0 e1
  simp [coeff_X, coeff_C] at e0 e1
  exact ⟨by linear_combination -e1, e0⟩
private theorem AuxBlock12 {k K : Type} [Field k] [Field K] (ι : k ≃+* K) (g : Matrix (Fin 3) (Fin 3) k) (α β γ : K)
    (h : g.charpoly.map ι.toRingHom = (X - C α) * (X - C β) * (X - C γ)) : ι g.trace = α + β + γ := by
  have e : ι g.trace = -(g.charpoly.map ι.toRingHom).coeff 2 := by
    rw [Matrix.trace_eq_neg_charpoly_coeff, coeff_map]
    simp
  have r : (X - C α) * (X - C β) * (X - C γ) =
      (X ^ 3 - C (α + β + γ) * X ^ 2 + C (α * β + α * γ + β * γ) * X - C (α * β * γ) : K[X]) := by
    simp only [C_add, C_mul]; ring
  rw [e, h, r]
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  norm_num
private theorem abs_ne_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 ≠ 1 := fun e => by
  have e' : absPow k (((1 : ℝ) : ℂ)) = absPow k (((0 : ℝ) : ℂ)) := by
    push_cast
    rw [e, absPow_zero]
  have := GlobalTheory.TypeTwo.absPow_ofReal_injective k _ _ e'
  norm_num at this
private theorem unl_two {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : Fin 2 → kˣ →* ℂˣ) (h : Reg (ψ 0 / ψ 1)) (i j : Fin 2) : ψ i ≠ ψ j * absPow k 1 := by
  have two : absPow k 2 = absPow k 1 ^ 2 := by
    rw [pow_two, ← absPow_add]; norm_num
  have h2 := h.2 2 (by norm_num)
  have h3 := h.2 (-2) (by norm_num)
  push_cast at h2 h3
  rw [absPow_neg, two] at h3
  rw [two] at h2
  have n1 := abs_ne_one k
  fin_cases i <;> fin_cases j
  · exact fun e => n1 (by simpa using e)
  · intro e
    apply h2
    simp only [Fin.zero_eta, Fin.mk_one] at e
    rw [e, mul_div_cancel_left]
  · intro e
    apply h3
    simp only [Fin.zero_eta, Fin.mk_one] at e
    rw [e, div_mul_cancel_left, inv_pow]
  · exact fun e => n1 (by simpa using e)
private theorem unl_three {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : kˣ →* ℂˣ) (h : Reg a) (i j : Fin 3) :
    (![a, 1, a⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ ![a, 1, a⁻¹] j * absPow k 1 := by
  by_cases e : i = j
  · subst e
    exact fun e => abs_ne_one k (by simpa using e)
  · exact ((Al.regUnl k a h).1.2 i j e).2
private theorem local_trace_compatible (P : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility) {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)) (r3 : G L Ω →* GL (Fin 3) (Qbar l))
    (σ : Submodule ℂ (UA L 2 → ℂ)) (σ₃ : Submodule ℂ (UA L 3 → ℂ)) (hg : GalT ι σ r) (hg3 : GalT ι σ₃ r3)
    (w : Plc L) (hw : IsSplitAt w) (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (ψ : Fin 2 → (Kw w)ˣ →* ℂˣ) (hE : CompEq σ w ψ)
    (hR : Reg (ψ 0 / ψ 1))
    (hS : CompSub σ₃ w ![ψ 0 / ψ 1, 1, (ψ 0 / ψ 1)⁻¹]) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (t : Weil h) :
    Ga.tr (r3 (t : G L Ω)) * Ga.ep l (t : G L Ω) = Ga.uf (r (t : G L Ω)) + 1 := by
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds L Ω A w h
  obtain ⟨hsm, τ, hτ, ⟨e⟩⟩ := hE
  obtain ⟨hsm3, τ3, hτ3, hq3⟩ := hS
  have hq2 : IsSubquotient τ.ρ (prinSeries ψ) :=
    IsSubquotient.of_surjective e.symm.toIntertwiningMap e.symm.surjective
  have p2 : PT τ := _root_.UpperTheory.V.Z.Sym.W.plain_of_statement P.af.litN L 2 w τ ψ hsm hq2 (unl_two ψ hR)
  have p3 : PT τ3 := _root_.UpperTheory.V.Z.Sym.W.plain_of_statement P.af.litN L 3 w τ3 _ hsm3 hq3 (unl_three _ hR)
  have c2 := _root_.UpperTheory.V.Z.Sym.W.eigW_alt P.af L Ω l ι 2 r w hl A h a ha τ (hg.loc w hw τ hτ) p2 ψ hsm hq2 t
  have c3 := _root_.UpperTheory.V.Z.Sym.W.eigW_alt P.af L Ω l ι 3 r3 w hl A h a ha τ3 (hg3.loc w hw τ3 hτ3) p3 _ hsm3 hq3 t
  have he := (_root_.UpperTheory.V.Z.Sym.Ga.cyc_char_eq_abs_pow_and_norm_pow_deg_away_l P.af L Ω l ι w hl A h a ha t).1
  rw [psPol, Fin.prod_univ_two] at c2
  rw [psPol, Fin.prod_univ_three] at c3
  obtain ⟨t2, d2⟩ := trace_det_of_charpoly_two ι _ _ _ c2
  have t3 := AuxBlock12 ι _ _ _ _ c3
  have hp : (-((((3 : ℕ) : ℂ) - 1) / 2)) = -1 := by norm_num
  rw [hp, absPow_neg] at t3
  apply ι.injective
  simp only [Ga.uf, Ga.tr, map_mul, map_add, map_sub, map_div₀, map_pow, map_one, map_ofNat]
  rw [t2, d2, t3, he]
  simp only [MonoidHom.mul_apply, MonoidHom.div_apply, MonoidHom.inv_apply, MonoidHom.one_apply, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val, Units.val_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hu := (ψ 0 (a t)).ne_zero
  have hv := (ψ 1 (a t)).ne_zero
  have hq := (absPow (w.adicCompletion L) (-((((2 : ℕ) : ℂ) - 1) / 2)) (a t)).ne_zero
  have he0 := (absPow (w.adicCompletion L) 1 (a t)).ne_zero
  field_simp
  ring
private theorem irr_of_open {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k}
    (h : IrrOpen r) : IsIrr r := by
  obtain ⟨h1, -, h3⟩ := h ⊤ (by simp)
  exact ⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hW => h3 W le_top (fun s v hv => hW s v hv)⟩
private theorem ss_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
    (h : RepIso r r') (hr : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) hr
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group
private theorem att_iso {F Ω : Type} [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {π : CuspSub F n}
    (h : RepIso r r') (H : AttC ι r π) : AttC ι r' π :=
  ⟨ss_iso h H.1, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩
theorem branch1W_alt : _root_.UpperTheory.V.Z.Sym.W.Branch1WAlt := by
  intro Pr L Ω _ _ _ _ _ _ l _ ι hl hU M m hM r σ hA hg P ψ hP hreg σ₃ hσ₃ hev
  obtain ⟨r3, hg3, hirr⟩ := _root_.UpperTheory.V.Z.Sym.W.galois_exists_w_statement Pr L Ω l ι hl hU 3 (by norm_num) σ₃ hσ₃
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  obtain ⟨hcu, hce, hbad⟩ := Ga.badClosed L Ω l r hg.cont
  have hct : Continuous fun g : G L Ω => Ga.tr (r3 g) :=
    Continuous.matrix_trace (Units.continuous_val.comp hg3.cont)
  let E : Set (G L Ω) := {g | Ga.tr (r3 g) * Ga.ep l g = Ga.uf (r g) + 1 ∧
    Ga.tr (r3 g⁻¹) * Ga.ep l g⁻¹ = Ga.uf (r g⁻¹) + 1}
  have hEc : IsClosed E :=
    IsClosed.inter (isClosed_eq (hct.mul hce) (hcu.add continuous_const))
      (isClosed_eq ((hct.comp continuous_inv).mul (hce.comp continuous_inv)) ((hcu.comp continuous_inv).add continuous_const))
  have hstab : ∀ c : G (maximalRealSubfield L) Ω, IsConjEl c → ∀ s s' : G L Ω,
      s'.restrictScalars (maximalRealSubfield L) = c * s.restrictScalars (maximalRealSubfield L) * c⁻¹ → s' ∈ E → s ∈ E := by
    intro c hc s s' hs hs'
    obtain ⟨h1, h2⟩ := hs'
    obtain ⟨P3, hP3⟩ := hg3.pair c hc
    obtain ⟨P2, hP2⟩ := hg.pair c hc
    have hi : (s'⁻¹ : G L Ω).restrictScalars (maximalRealSubfield L) =
        c * (s⁻¹ : G L Ω).restrictScalars (maximalRealSubfield L) * c⁻¹ := by
      have e : ∀ x : G L Ω, (x⁻¹ : G L Ω).restrictScalars (maximalRealSubfield L) =
          (x.restrictScalars (maximalRealSubfield L))⁻¹ := fun _ => rfl
      rw [e, e, hs]
      group
    have hes : Ga.ep l s' = Ga.ep l s := by
      have e : ∀ x : G L Ω, cycBar L Ω l x = cycBar (maximalRealSubfield L) Ω l (x.restrictScalars (maximalRealSubfield L)) :=
        fun _ => rfl
      simp only [Ga.ep]
      rw [e s', e s, hs, map_mul, map_mul, map_inv, mul_comm (cycBar _ Ω l c), mul_inv_cancel_right]
    have hei : ∀ g : G L Ω, Ga.ep l g⁻¹ = (Ga.ep l g)⁻¹ := by
      intro g
      simp [Ga.ep]
    have hne : Ga.ep l s ≠ 0 := Units.ne_zero _
    have hμ : ∀ g : G L Ω, (((cycBar L Ω l ^ (1 - ((3 : ℕ) : ℤ))) g : (Qbar l)ˣ) : Qbar l) = (Ga.ep l g ^ 2)⁻¹ := by
      intro g
      have e : (1 - ((3 : ℕ) : ℤ)) = -2 := by norm_num
      rw [e]
      simp [Ga.ep, zpow_neg]
    have a1 := Ga.trPair _ 3 (r3 s) (r3 s') P3 _ (hP3 s s' hs)
    have a2 := Ga.trPair _ 3 (r3 s⁻¹) (r3 s'⁻¹) P3 _ (hP3 _ _ hi)
    rw [hμ, ← map_inv] at a1
    rw [hμ, ← map_inv, inv_inv] at a2
    have u1 := (Ga.ufFacts _ (r s)).2.2.2.1 (r s') P2 _ (hP2 s s' hs)
    have u2 : Ga.uf (r s⁻¹) = Ga.uf (r s) := by
      rw [map_inv]
      exact (Ga.ufFacts _ (r s)).2.1
    have u3 : Ga.uf (r s'⁻¹) = Ga.uf (r s') := by
      rw [map_inv]
      exact (Ga.ufFacts _ (r s')).2.1
    refine ⟨?_, ?_⟩
    · rw [u3, u1, a2] at h2
      simp only [hei, hes] at h2
      rw [← h2]
      field_simp
    · rw [a1, hes, u1] at h1
      rw [u2, ← h1, hei]
      field_simp
  have hfrob : ∀ᶠ w in Filter.cofinite, w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E := by
    filter_upwards [hev] with w hw hwP s hs
    obtain ⟨A, hAw, hF⟩ := hs
    obtain ⟨hsp, hlw, hc⟩ := hP.mem w hwP
    have hW := mem_Weil_of_isFrob hAw hF
    exact ⟨local_trace_compatible Pr ι r r3 σ σ₃ hg hg3 w hsp hlw (ψ w) hc (hreg w hwP) (hw hwP) A hAw ⟨s, hW⟩,
      local_trace_compatible Pr ι r r3 σ σ₃ hg hg3 w hsp hlw (ψ w) hc (hreg w hwP) (hw hwP) A hAw ⟨s⁻¹, inv_mem hW⟩⟩
  have hsub := Ga.spread L Ω hU E (Ga.Bad r) hEc hbad hstab P M hM hP.meets hfrob
  obtain ⟨s0, -, hs0, -⟩ := _root_.UpperTheory.V.Z.Sym.Ga.exists_regular_elt_in_open_subgroup_infinite_order L Ω l ι M m r hA.toIn_alt ⊤ isOpen_univ
  have hRo : IrrOpen (tw (ad0 r) (cycBar L Ω l)⁻¹) := fun H hH =>
    (Sd.shapeFacts l H 3 ((ad0 r).comp H.subtype) ((cycBar L Ω l)⁻¹.comp H.subtype)).2.2.2.2.2
      (Sd.ad0Irr l (G L Ω) r hg.cont hA.irr H hH)
  have htr : ∀ g ∈ (Ga.Bad r)ᶜ, Ga.tr (r3 g) = Ga.tr (tw (ad0 r) (cycBar L Ω l)⁻¹ g) :=
    (fun g hg' => by
      have h1 := (hsub hg').1
      have h2 := (Ga.ufFacts _ (r g)).2.2.2.2 _ r g
      have e3 : ((((cycBar L Ω l)⁻¹ g : (Qbar l)ˣ)) : Qbar l) = (Ga.ep l g)⁻¹ := by simp [Ga.ep]
      have hne : Ga.ep l g ≠ 0 := Units.ne_zero _
      have e4 : Ga.tr (tw (ad0 r) (cycBar L Ω l)⁻¹ g) = (Ga.ep l g)⁻¹ * Ga.tr (ad0 r g) := by
        simp only [Ga.tr, tw_val, Matrix.trace_smul, smul_eq_mul, e3]
      rw [e4, h2, ← h1]
      field_simp)
  obtain ⟨ξ, hξ, hiso⟩ := Ga.twistOf l (G L Ω) 3 (tw (ad0 r) (cycBar L Ω l)⁻¹) r3 hRo (Ga.Bad r)ᶜ hbad.isOpen_compl ⟨s0, hs0⟩ htr
  have h4 := Ga.sym4Irr l (G L Ω) r hg.cont hA.irr fun H hH => by
    obtain ⟨s, hs, -, h⟩ := _root_.UpperTheory.V.Z.Sym.Ga.exists_regular_elt_in_open_subgroup_infinite_order L Ω l ι M m r hA.toIn_alt H hH
    exact ⟨s, hs, h⟩
  have hone : ξ = 1 := U.xiOne L Ω l r hg.cont h4 ξ hξ fun g hg' => by
    obtain ⟨x, hx⟩ := hiso
    have h1 := htr g hg'
    have h2 := (Ga.ufFacts _ (r g)).2.2.2.2 _ r g
    have h3 : Ga.tr (r3 g) = (ξ g : Qbar l) * Ga.tr (tw (ad0 r) (cycBar L Ω l)⁻¹ g) := by
      rw [hx g]
      simp only [Ga.tr]
      rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
        tw_val (tw (ad0 r) (cycBar L Ω l)⁻¹), Matrix.trace_smul, smul_eq_mul]
    have e4 : Ga.tr (tw (ad0 r) (cycBar L Ω l)⁻¹ g) = (((cycBar L Ω l)⁻¹ g : (Qbar l)ˣ) : Qbar l) * Ga.tr (ad0 r g) := by
      simp only [Ga.tr, tw_val, Matrix.trace_smul, smul_eq_mul]
    rw [h3, e4, h2] at h1
    refine mul_left_cancel₀ ((cycBar L Ω l)⁻¹ g).ne_zero ?_
    rw [← h1]
    ring
  have e : tw (tw (ad0 r) (cycBar L Ω l)⁻¹) ξ = tw (ad0 r) (cycBar L Ω l)⁻¹ := by
    ext g : 2
    rw [tw_val, hone]
    simp
  rw [e] at hiso
  have hI := _root_.UpperTheory.V.Z.Sym.Ga.isAutC_isAutCsdA_isIrr_irrOpen_symm_tw_of_repIso L Ω l ι 3 _ r3 hiso
  obtain ⟨π, a1, a2, a3, a4⟩ := hirr (irr_of_open (hI.2.2.2.1 hRo))
  exact ⟨π, a1, a2, att_iso hI.2.2.2.2.1 a3, a4⟩
end UpperTheory.V.Z.Sym.W
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCountE
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing Filter GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem ce_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)
private theorem ce_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := ce_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
  rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
private theorem ce_open {G O : Type} [Group G] [TopologicalSpace G] [CommRing O] {m : ℕ} (f : O →+* ℂ) (hf : Function.Injective f)
    (τ : G →* GL (Fin m) O) (h : IsOpen (((Matrix.GeneralLinearGroup.map f).comp τ).ker : Set G)) : IsOpen (τ.ker : Set G) := by
  have : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker := by
    refine MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_
    ext i j
    exact hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)
  rwa [this] at h
private theorem ce_ex {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z : Submodule ℂ M)
    (hf : FiniteDimensional ℂ Z) (hZ : Z ≠ ⊥) (hsum : Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z)) :
    ∃ i, Y i ⊓ Z ≠ ⊥ := by
  by_contra h
  push Not at h
  apply hZ
  rw [← Submodule.finrank_eq_zero, hsum]
  exact Finset.sum_eq_zero fun i _ => by rw [h i, finrank_bot]
private def ce_mk {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {n : ℕ} {s : HidaSetting l L Ω} (V : s.Lev) (hS : ∀ v ∈ s.S, IsSplitAt (s.w v)) (τ : ∀ w : Plc L, SmIrr (GLw n w))
    (σ : Submodule ℂ (UA L n → ℂ)) (h : ∀ w, IsSplitAt w → Cp σ w (τ w)) : Comps V σ where
  l v := τ (s.w v.1)
  u v := τ (s.w v)
  o := τ (s.w s.v0)
  hl v := h _ (hS _ (Or.inl v.2))
  hu v := h _ (hS _ (Or.inr (Or.inl v.2)))
  ho := h _ (hS _ (Or.inr (Or.inr rfl)))
private theorem ce_ne {M : Type} [AddCommGroup M] [Module ℂ M] {Y Z : Submodule ℂ M} (h : Y ⊓ Z ≠ ⊥) : Y ≠ ⊥ :=
  fun h' => h (by rw [h', bot_inf_eq])
section Set
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l}
  {H : HSet L Ω l n c} {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] {θ : H.X.I.T →* Aˣ} {ι : Qbar l ≃+* ℂ}
  {x : A →+* Qbar l} {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} {c0 : ℕ}
  {sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d}
private theorem ce_fin (hsp : H.IsSpec θ ι x lam ξ c0 sp) (K : H.Lev) (ev : H.Op → ℂ) :
    FiniteDimensional ℂ (zPart H θ ι x lam ξ K c0 ev) :=
  haveI := hsp.fin K c0 le_rfl
  Submodule.finiteDimensional_of_le (S₂ := H.ClAt θ ι x lam ξ K c0) (inf_le_left.trans (iSup_le fun _ => inf_le_left))
private theorem ce_one (hSl : Slope) (hO1 : _root_.UpperTheory.V.Z.J.D.Ord1Alt) (hEP : EigPi) (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hAx : H.Ax)
    (hsp : H.IsSpec θ ι x lam ξ c0 sp) (ev : H.Op → ℂ) (hev : ∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1)
    (τ : ∀ v, SmIrr (GLw n (H.Sl v))) :
    Module.rank ℂ (eigL H.Sl (piRep fun v => (τ v).ρ) c0 (fun v i y => (ι (H.finPart θ x lam v i y))⁻¹)
      fun v j => H.lowVal ι lam v (j + 1) * ev (.inr (v, j))) ≤ 1 := by
  refine hEP L n H.V H.Sl τ c0 _ _ fun v => ?_
  refine hO1 N _ n _ _ (τ _).smooth (τ _).irred c0 _ _ (fun i y hy => ?_)
    (hSl L Ω l n c H hAx ι lam v (fun j => ev (.inr (v, j))) (hev v))
  rw [hsp.triv v i y hy, map_one, inv_one]
end Set
section Stg
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  (s : HidaSetting l L Ω)
private theorem ce_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)
private theorem ce_split (w : Plc L) (h : w.under (𝓞 (Lp L)) ∈ s.S) : IsSplitAt w :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A _) _ (s.hA _) (s.split _ h) w rfl
private theorem ce_S (v : Plc (Lp L)) (h : v ∈ s.S) : IsSplitAt (s.w v) := ce_split s _ ((ce_w s v).symm ▸ h)
private theorem ce_irr (V : s.Lev) {n : ℕ} (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (hi : Af.IsIrr ρ) : Af.IsIrr (ρ.comp V.pr) := by
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, ReciprocityTheory.Gal.toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨t, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨t, Subtype.ext hτ⟩
  refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M hM hI => hi.2.2 M hM fun g => ?_⟩
  obtain ⟨g, rfl⟩ := hpr g
  exact hI g
end Stg
private theorem eigenpart_zero_eq_top {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ (0 : G →₀ ℤ) 0 = ⊤ := by
  simp [ePart, opE]
private theorem ce_top {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z E : Submodule ℂ M) (hE : E = ⊤)
    (hsum : Module.finrank ℂ ↥(Z ⊓ E) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E)) :
    Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z) := by
  subst hE
  have h : ∀ S : Submodule ℂ M, Module.finrank ℂ ↥(S ⊓ ⊤) = Module.finrank ℂ S := fun S => by rw [inf_top_eq]
  simpa only [h] using hsum
private theorem cardinal_factor_eq_one {M : Type} [AddCommGroup M] [Module ℂ M] (Y Z ZL E : Submodule ℂ M) (hE : E = ⊤) (h0 : Y ⊓ Z ≠ ⊥) (h2 : Y ⊓ Z = Y ⊓ ZL)
    (a b : Cardinal) (ha : a ≤ 1) (h3 : Module.rank ℂ ↥(Y ⊓ ZL ⊓ E) = a * b) : a = 1 := by
  subst hE
  rcases Cardinal.le_one_iff.1 ha with h | h
  · rw [h, zero_mul, Submodule.rank_eq_zero, inf_top_eq, ← h2] at h3
    exact absurd h3 h0
  · exact h
private theorem ce_cnt {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z ZL E : Submodule ℂ M)
    (hf : FiniteDimensional ℂ Z) (hsum : Module.finrank ℂ ↥(Z ⊓ E) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E)) (P : J → Prop)
    (a b : Cardinal) (k : ℕ) (h1 : ∀ i, Y i ⊓ Z ≠ ⊥ → P i) (h2 : ∀ i, P i → Y i ⊓ Z = Y i ⊓ ZL) (ha1 : a = 1)
    (h3 : ∀ i, P i → Module.rank ℂ ↥(Y i ⊓ ZL ⊓ E) = a * b) (hk : Nat.card {i // P i} = k) :
    (Module.finrank ℂ ↥(Z ⊓ E) : Cardinal) = k * b := by
  classical
  have h6 : ∀ i, (Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E) : Cardinal) = if P i then b else 0 := fun i => by
    haveI : FiniteDimensional ℂ ↥(Y i ⊓ Z ⊓ E) := Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_right)
    rw [Module.finrank_eq_rank]
    split_ifs with h
    · rw [h2 i h, h3 i h, ha1, one_mul]
    · rw [Submodule.rank_eq_zero]
      by_contra h'
      refine h (h1 i fun h'' => h' ?_)
      rw [h'', bot_inf_eq]
  rw [hsum, Nat.cast_sum, Finset.sum_congr rfl fun i _ => h6 i, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hk,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.Desc.V0.count_e_of_sph_same_at_same_bc_dims :
    UpperTheory.V.Z.J.D.WtEx → UpperTheory.V.Z.J.D.Decomp → ZDecE → UpperTheory.V.Z.J.D.ZEq → _root_.UpperTheory.V.Z.J.D.SphSameAlt → _root_.UpperTheory.V.Z.J.D.AtSameAlt → _root_.UpperTheory.V.Z.J.D.BcOfAlt → YDimE → UpperTheory.V.Z.J.D.CompsEx → UpperTheory.V.Z.J.D.Slope → _root_.UpperTheory.V.Z.J.D.Ord1Alt → UpperTheory.V.Z.J.D.EigPi → _root_.UpperTheory.V.Z.Desc.V0.CountEAlt := by
  intro hWt hDec hZD _ hSph hAt hBc hYD _ hSl hO1 hEP PH hM hCO l _ L Ω _ _ _ _ _ _ s n hn V hV h4 ι lam
  have N := PH.toClassicalTheorems.litN
  have hU : GlobalTheory.BCT.Unr L := UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr
  obtain ⟨lam', hl'⟩ := hWt l L Ω s n hn V hV ι lam
  obtain ⟨a₀, -, ha⟩ := hM L hU n hn h4 lam'
  refine ⟨a₀, ?_⟩
  intro Q c r m τ₀ hτ d e ξ he A _ _ _ θ x c0 sp hθ hsp K ev hev hZ hP
  have hAx := _root_.UpperTheory.V.Hi.axU_s N l L Ω s n hn V Q c m τ₀
  have hS := ce_S s
  obtain ⟨t, ht⟩ := ce_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    ce_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  obtain ⟨S, K', J, _, σ, hSec, hLev, hKL, hID, hInd, hUn, hFix, hLe⟩ :=
    hDec l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he hop lam' hl' c0
  have hA : ∀ i, IsAutRepU (σ i) := fun i => (hID.1 i).1
  have hsumE := fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) (h : ∀ g ∈ a.support, g ∈ KO _ (Fin n)) =>
    hZD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev J σ hA hInd hLe a N h
  have he0 : eC Q τ₀ d (0 : GLw n (s.w s.v0) →₀ ℤ) 0 = ⊤ := eigenpart_zero_eq_top _
  have hsum := ce_top (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ he0 (hsumE 0 0 (by simp))
  have hfin := ce_fin hsp K ev
  obtain ⟨i0, h0⟩ := ce_ex (fun i => YOf Q ι τ₀ e ξ (σ i)) _ hfin hZ hsum
  have hY0 : YOf Q ι τ₀ e ξ (σ i0) ≠ ⊥ := ce_ne h0
  obtain ⟨Y, hY, -, -, hLG⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt PH l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he (σ i0) (hA i0) hY0
  have hi := hP Y (by rw [hY]; exact h0)
  have hc : Continuous (Y.r.comp V.pr) := Y.cont.comp (V.pr_cont W.continuous_resP)
  obtain ⟨π, hreg, hcsd, hat, hinf, hsat⟩ := hBc PH L Ω hU l s.odd ι n hn (σ i0) (hA i0) (Y.r.comp V.pr) hc (ce_irr s V Y.r hi)
    (Eventually.of_forall hLG)
  have hns : ∀ w : Plc L, ¬ IsSplitAt w → w.under (𝓞 (Lp L)) ∉ s.S := fun w h h' => h (ce_split s w h')
  choose τ hτπ using fun w => (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PH.toClassicalTheorems L n π w).1
  have hCp : ∀ i, At π (σ i) → ∀ w, IsSplitAt w → Cp (σ i) w (τ w) := fun i h w hw =>
    hCO L hU n hn h4 π hreg hcsd (σ i) (hA i) (fun w hw => hUn i w (hns w hw)) h w hw _ (hτπ w)
  have hcard := ha π hreg hcsd (fun v => hinf _ _ ((hID.1 i0).2.1 v)) (fun w hw => hsat w (hUn i0 w (hns w hw))) S hSec K' hLev
    (fun w hw => hKL w (hns w hw)) (fun w hwS hw => ⟨τ w, hτπ w, hFix i0 w hwS hw _ (hCp i0 hat w hw)⟩) J σ hID
  have h1 := fun i h => hAt N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev _ _ (hA i0) (hA i) h0 h π hat
  have h2 := fun i (h : At π (σ i)) => hSph N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev _ _ (hA i0) (hA i)
      (fun w hw => ⟨τ w, hCp i0 hat w hw, hCp i h w hw⟩) h0
  have h3 := fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) i (h : At π (σ i)) =>
    hYD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he (σ i) (hA i) (hUn i) ((hl' _ (hA i)).2 (hID.1 i).2.1)
      (ce_mk V hS τ (σ i) (hCp i h)) c0 (fun v i y => (ι ((hset Q τ₀).finPart θ x.toRingHom lam v i y))⁻¹)
      (fun v j => (hset Q τ₀).lowVal ι lam v (j + 1) * ev (.inr (v, j))) a N
  have h5 := ce_one hSl hO1 hEP N hAx hsp ev hev fun v => τ (s.w v.1)
  have ha1 := cardinal_factor_eq_one _ _ _ _ he0 h0 (h2 i0 hat) _ _ h5 (h3 0 0 i0 hat)
  refine ⟨π, σ i0, ce_mk V hS τ (σ i0) (hCp i0 hat), fun u => hτπ _, hτπ _, hY0, hA i0, fun a N' hs => ?_⟩
  exact ce_cnt (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ _ hfin (hsumE a N' hs) (fun i => At π (σ i)) _ _ a₀ h1 h2 ha1 (h3 a N') hcard
end
end

