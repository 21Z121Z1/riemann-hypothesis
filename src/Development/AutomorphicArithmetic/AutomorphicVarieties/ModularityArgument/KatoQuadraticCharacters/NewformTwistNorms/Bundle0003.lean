import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewVec
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

open private UpperTheory.V.Af.Nf.liftHol from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf

namespace UpperTheory.V.Z.Kato.NewVec

open UpperTheory.V.Sd

private theorem comp_zero {V : Type} [AddCommGroup V] [Module ℂ V] {U W : Submodule ℂ V} (hd : Disjoint U W) (T : Module.End ℂ V)
    (hU : ∀ x ∈ U, T x ∈ U) (hW : ∀ x ∈ W, T x ∈ W) {φ ψ : V} (hψ : ψ ∈ U) (hm : φ - ψ ∈ W) (h0 : T φ = 0) : T ψ = 0 := by
  refine Submodule.disjoint_def.1 hd _ (hU _ hψ) ?_
  have := W.neg_mem (hW _ hm)
  rwa [map_sub, h0, zero_sub, neg_neg] at this

private noncomputable abbrev Eo (v : InfinitePlace ℚ) (i j : Fin 2) : Module.End ℂ (TR.Sm ℚ 2) := TR.Eop v i j

private theorem eop_mem {U : Submodule ℂ (TR.Sm ℚ 2)} (hU : TR.IsStable U) (v : InfinitePlace ℚ) (i j : Fin 2) :
    ∀ x ∈ U, TR.Eop v i j x ∈ U := fun x hx => hU (.lie _) x hx

private theorem eop_one (v : InfinitePlace ℚ) (φ : TR.Sm ℚ 2) :
    TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = TR.lie ℚ 2 (TR.oneL ℚ 2) φ := by
  classical
  rw [TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]
  congr 2
  ext i j w
  obtain rfl : w = v := Subsingleton.elim _ _
  fin_cases i <;> fin_cases j <;> simp

theorem newVec : Published.CuspSemisimpleReal → Published.AdmissibleReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k), ∃ (π₀ : TR.CuspSub ℚ 2) (ψ : TR.Sm ℚ 2), ψ ∈ π₀.V ∧ ψ ≠ 0 ∧ (∀ q : HeightOneSpectrum (𝓞 ℚ), ψ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev g.M q))) ∧ ((∀ v, TR.Eop v 0 1 ψ - TR.Eop v 1 0 ψ = (Complex.I * (k : ℂ)) • ψ) ∧ (∀ v, TR.Eop v 0 0 ψ - TR.Eop v 1 1 ψ = Complex.I • (TR.Eop v 0 1 ψ + TR.Eop v 1 0 ψ)) ∧ (∀ v, TR.Eop v 0 0 ψ + TR.Eop v 1 1 ψ = 0)) ∧ ∀ q : HeightOneSpectrum (𝓞 ℚ), ¬ normV q ∣ g.M → ∃ α β : ℂˣ, π₀.HasSat q {α, β} ∧ (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = g.a (normV q) ∧ ((α * β : ℂˣ) : ℂ) = g.χ (normV q : ZMod g.M) := by
  intro hS hA k hk2 f
  have hM : 1 ≤ f.M := f.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ω, hω⟩ := dirChar f.M hM f.χ
  obtain ⟨hfin, hval⟩ := charVal f.M hM f.χ ω hω
  obtain ⟨φ, hL, hH, hC⟩ := UpperTheory.V.Af.Nf.liftHol k f.M hM f.χ ω hω f.f f.char
  have hE := liftExp k f.M hM f.f φ.1 hL
  obtain ⟨-, hz, hl1, hl2, -⟩ := holLin ℚ k (lev f.M) ω
  have h0 : φ ≠ 0 := by
    rintro rfl
    have := (expUnique ℚ _ k _ _ _ _ hE hz).2 ⊤ top_ne_bot
    rw [icoef, Ideal.absNorm_top, f.one] at this
    exact one_ne_zero this
  obtain ⟨h1, -⟩ := holCap ℚ k _ ω hfin φ hH
  obtain ⟨π, ψ, W, hψ, hW, hd, hm⟩ := split ℚ 2 φ h0 (hS ℚ 2 φ hC ⟨0, by rw [h1, zero_smul]⟩)
  have hπ : TR.IsStable π.V := π.stable
  refine ⟨π, ψ.1, ψ.2, fun e => hψ (Subtype.ext e), fun q u hu => ?_, ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩, fun w hw => ?_⟩
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U, (locSm ℚ q u - 1 : Module.End ℂ _) x ∈ U :=
      fun U hU x hx => U.sub_mem (hU (.fin (locGL ℚ 2 q u)) x hx) hx
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.level q u hu)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2))) x ∈ U :=
      fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)) (U.smul_mem _ hx)
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.wt v)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0)) x ∈ U :=
      fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx))
        (U.smul_mem _ (U.add_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)))
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.low v)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 0 + Eo v 1 1) x ∈ U :=
      fun U hU x hx => U.add_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx)
    exact comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm ((eop_one v φ).trans h1)
  · have hc := (places w).2.2.2 f.M hM hw
    obtain ⟨h1, -, h2⟩ := holHk ℚ k hk1 _ ω hfin φ hH w
    obtain ⟨c₀, h3⟩ := h2 _ _ hE
    have h4 := expInj ℚ k hk1 _ ω hfin _ (hl1 _ _ (-f.a (normV w)) h1 hH) _ _ (hl2 _ _ (-f.a (normV w)) _ _ _ _ h3 hE)
      fun 𝔪 h𝔪 => by simp [hkCoef k f ω w hw (hval w hw) 𝔪 h𝔪]
    rw [hc, neg_smul, add_neg_eq_zero] at h4
    obtain ⟨α, β, hv, hsum, hprod⟩ := satHol ℚ k _ ω φ hH h0 w _ hc h4
    exact ⟨α, β, satOfVec hA ℚ 2 π w ψ _ (satComp ℚ φ π ψ W hψ hW hd hm w _ hv), hsum, by rw [hprod, hval w hw]⟩

end UpperTheory.V.Z.Kato.NewVec
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformFlagLocalOfIrreducible
section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.UnramAtL

theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem place_unique (l : ℕ) [hl : Fact l.Prime] {v w : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have hpr : Prime (l : 𝓞 ℚ) := by
    have e : (l : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (l : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hl.out)
  have hm : (Ideal.span {(l : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  exact HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))

end GlobalTheory.Ord2.UnramAtL

open GlobalTheory.Ord2.UnramAtL in

theorem GlobalTheory.Ord2.unram_at_l : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → AttR ι V π → ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ∃ Bs, π.HasSat w Bs := by
  intro P l _ Ω _ _ _ ι e V A κ g hl he hcont hirr hAway hKill hOver hfl hκ _ π hreg hatt w hw
  obtain ⟨M, hM, haway⟩ := hAway
  obtain ⟨M', hM', hkill⟩ := hKill
  obtain ⟨v, hAv, hlv⟩ := hOver
  obtain rfl : w = v := place_unique l hw hlv
  have hAl : A.valuation (l : Ω) < 1 := by simpa using (hAv _).2 hlv
  let m : Fin 2 → ℤ := ![(e : ℤ), -(e : ℤ)]
  have hκm : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ i s = cycBar ℚ Ω l s ^ m i * (1 : G ℚ Ω →* (Qbar l)ˣ) s := by
    intro i s hs
    fin_cases i
    · simpa [m] using (hκ s hs).1
    · simpa [m] using (hκ s hs).2
  have hor : ∀ i j, κ i ≠ κ j * (cycBar ℚ Ω l).comp (Dec (F := ℚ) A).subtype := by
    intro i j hij
    obtain ⟨s, hs, hne⟩ := UpperTheory.V.Ws.Pt.cycIne ℚ Ω l A hAl (m i - m j - 1) (by
      fin_cases i <;> fin_cases j <;> simp [m] <;> omega)
    have h1 := congrArg (fun f => f ⟨s, Ine_le_Dec A hs⟩) hij
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
    rw [hκm i _ hs, hκm j _ hs] at h1
    apply hne
    simp only [MonoidHom.one_apply, mul_one] at h1
    rw [zpow_sub, zpow_sub, h1, zpow_one]
    group
  have hlev : Level l M m V := ⟨hcont, haway, fun w' hw' => by
    obtain rfl : w = w' := place_unique l hlv hw'
    exact ⟨A, hAv, fun _ => 1, κ, fun _ _ _ => rfl, hfl, hκm, Or.inl hor⟩⟩
  have hdual : ∃ θ, IsCycWt l 0 θ ∧ DualTw V θ :=
    ⟨dt V, ⟨M', dt V, hM', hkill, by simp⟩, dualTw_det V⟩
  have hanti : StrictAnti m := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [m] at hij ⊢ <;> omega
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.litN.loc.llc P.litN.loc.conv P.litN.loc.dzc P.litN.loc.dzi
      P.litN.loc.brauer P.litN.loc.chev P.litN.aut.art P.litN.loc.exh P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel
      P.litN.loc.geo P.litN.loc.bz
  obtain ⟨rc, hrc, -⟩ := hL.1 ℚ Ω A w hAv
  obtain ⟨j, L0, hj, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l ℚ Ω w A hw hAv
  obtain ⟨Bw, hBj, -⟩ := hB L0 le_rfl
  have hI : GlobalTheory.Pst.Induces Bw := fun x => by rw [hBj]; exact hj x
  obtain ⟨c1, c2⟩ := compatAtLQ P 2 le_rfl 0 l hl Ω ι V π hcont hirr M m hM hanti hlev hdual hreg hatt w A hAv _ Bw hI
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P ℚ 2 π w
  obtain ⟨x, hx0, hx⟩ := Lev.fixedAll P ℚ Ω l ι 2 1 le_rfl m V hcont w A hAv _ Bw hI κ
    ⟨fun _ => 1, fun _ _ _ => rfl, hfl, hκm⟩ c1 rc hrc σ
    (fun ⟨μ, hμ⟩ => c2 σ hσ rc hrc (Or.inl ((Lev.ssCalc ℚ Ω A w hAv).1 2 _ μ hμ))) (Or.inr (Or.inl hor))
  have hK : HasFixed σ.ρ (GlobalTheory.LFun.KGL w 2) := ⟨x, hx0, fun u hu => hx u (locGL_mem_KLev 2 w (by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top) hu)⟩
  obtain ⟨B, hB⟩ := (satLoc P ℚ 2 w σ).1 hK
  exact ⟨B, ((satLoc P ℚ 2 w σ).2 _ π.finPart (hiso σ hσ) B).2 hB⟩

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_flag_local_of_irreducible : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → AttR ι V π → ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ∃ Bs, π.HasSat w Bs := by
  first | exact @GlobalTheory.Ord2.unram_at_l | exact GlobalTheory.Ord2.unram_at_l | (intros; apply GlobalTheory.Ord2.unram_at_l <;> assumption)

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.OrdinaryFlagInertiaWeights
section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrobRec

open Polynomial

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem rec_algNorm_diag {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  obtain ⟨hu, -⟩ := GlobalTheory.RecLaws.rec_hasSatGL H σ B hB
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    ParLaws.rec_eq_diag H hα
  rw [rec_algNorm H, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring

end GlobalTheory.FrobRec

open GlobalTheory.FrobRec Polynomial in

theorem GlobalTheory.recFrob_root_inv_algSat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
    ∀ φ : ↥(Weil h), deg φ = 1 → ∀ z : ℂ, (WD.charPol (rc (algNorm σ)) φ).IsRoot z →
      ∃ b ∈ algSat n (normV w) B, z * b = 1 := by
  intro E Ω _ _ _ _ _ A w h rc H n σ B hB φ hd z hz
  obtain ⟨α, rfl, e⟩ := rec_algNorm_diag H σ B hB
  rw [e, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd] at hz
  rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, -, hi⟩ := hz
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, zpow_one] at hi
  refine ⟨((((α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ), ?_, ?_⟩
  · rw [val_inv_eq, algSat, Multiset.mem_map]
    refine ⟨(α i : ℂ), ?_, rfl⟩
    simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map]
    exact Multiset.mem_map_of_mem (fun j => ((α j : ℂˣ) : ℂ)) (Finset.mem_univ i)
  · rw [hi, zpow_neg_one, mul_inv_cancel₀ (Units.ne_zero _)]

end

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_roots_local_correspondence : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
    ∀ φ : ↥(Weil h), deg φ = 1 → ∀ z : ℂ, (WD.charPol (rc (algNorm σ)) φ).IsRoot z →
      ∃ b ∈ algSat n (normV w) B, z * b = 1 := by
  first | exact @GlobalTheory.recFrob_root_inv_algSat | exact GlobalTheory.recFrob_root_inv_algSat | (intros; apply GlobalTheory.recFrob_root_inv_algSat <;> assumption)

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.WeilDeligneFrobeniusEigenvalueOfFullFlag
section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Module UpperTheory.V.Af.Wd

namespace GlobalTheory.FlagFrob

private theorem cont_diag {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} (hr : Continuous r) {H : Subgroup Γ} {κ : Fin n → ↥H →* (Qbar l)ˣ}
    (hf : IsFlagOn r H κ) (i : Fin n) : Continuous fun s => (κ i s : Qbar l) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s : ↥H => (g * r s * g⁻¹ : GL (Fin n) (Qbar l)) :=
    (continuous_const.mul (hr.comp continuous_subtype_val)).mul continuous_const
  exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (hg s).2 i

private theorem isRoot_of_tri {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ}
    (b : Basis (Fin n) ℂ W) (f : End ℂ W) (d : Fin n → ℂ)
    (h0 : ∀ i j, j < i → LinearMap.toMatrix b b f i j = 0) (h1 : ∀ i, LinearMap.toMatrix b b f i i = d i)
    (i : Fin n) : f.charpoly.IsRoot (d i) := by
  rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h0 i j hij),
    Polynomial.IsRoot, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h1])

set_option maxHeartbeats 800000 in

theorem isRoot_charPol_wdAt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ∀ (i : Fin n) (φ : ↥(Weil h)), deg φ = 1 →
        (WD.charPol (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) φ).IsRoot
          (((normV w : ℕ) : ℂ) ^ m i * ι ((κ i (Subgroup.inclusion (Weil_le_Dec h) φ) *
            cycBar F Ω l (φ : G F Ω) ^ (-m i) : (Qbar l)ˣ) : Qbar l)) := by
  rintro F Ω _ _ _ _ _ l _ ι n M hM m r hr w A h O _ _ _ Bw hj κ ⟨χ, hχ, hfl, hI⟩ hp i φ hφ
  have hκc := cont_diag hr hfl
  obtain ⟨L, ρ, κL, χL, hV, e, htri, hκ, hχL⟩ := UpperTheory.galois_representation_model_over_finite_extension F Ω l ι n r w A h O Bw hj κ χ
    (fun i => UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ (hχ i)) hfl hp
  obtain ⟨-, hcyc, hK⟩ := UpperTheory.crystalline_period_ring_properties F Ω l w A h O Bw hj
  obtain ⟨K', hK'⟩ := hK M hM
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype
  let ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ := fun i => κ i * ε ^ (-m i)
  let μ : ↥(Weil h) → Fin n → ℂ := fun σ i => ((normV w : ℕ) : ℂ) ^ (m i * deg σ) * ι (ψ i (inc σ) : Qbar l)
  have hεc : Continuous fun s => (ε s : Qbar l) := by
    have h0 : Continuous fun g : GQ l => (((Loc.PP l).χQ g : ℚ_[l]ˣ) : ℚ_[l]) := by
      obtain ⟨hc, -, hq⟩ := Loc.cycFacts l l
      simp only [hq]
      have h0 : Continuous fun g : GQ l => ((Loc.cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) := Units.continuous_val.comp hc
      exact continuous_subtype_val.comp h0
    exact ((continuous_algebraMap ℚ_[l] (Om l)).comp (h0.comp (continuous_subtype_val.comp Bw.e_cont))).congr
      fun s => hcyc L s
  have hψc : ∀ i, Continuous fun s => (ψ i s : Qbar l) := fun i => by
    refine ((hκc i).mul (hεc.zpow₀ (-m i) fun s => Or.inl (Units.ne_zero _))).congr fun s => ?_
    simp [ψ]
  haveI := hV.finite
  have T := UpperTheory.weilDeligne_triangularizable F Ω l ι w A h O Bw hj L n _ ρ κL μ htri (fun i hi σ y => by
    refine (UpperTheory.cyclotomicWeilChar_properties F Ω l ι w A h O Bw hj L (κL i) (χL i) (m i) ?_ ⟨K', fun g hg => ?_⟩ (fun g hg => ?_) hi σ y).trans ?_
    · refine ((hκc i).comp Bw.e_symm_cont).congr fun g => ?_
      rw [Function.comp_apply, ← hκ, MulEquiv.apply_symm_apply]
    · obtain ⟨s, rfl⟩ := Bw.e.surjective g
      refine Units.ext (Subtype.ext ?_)
      rw [hχL, hχ i s (hK' s hg)]
      rfl
    · obtain ⟨s, rfl⟩ := GlobalTheory.PstLaws.exists_ine_of_fix Bw h hj g hg
      refine Units.ext (Subtype.ext ?_)
      have h1 := congrArg Units.val (hI i (inc (ineIncl h s)) s.2)
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, ← hκ, ← hχL, ← hcyc L] at h1
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      exact h1.trans (by congr 1)
    · congr 3
      have h1 : (ψ i (inc σ) : Qbar l) = (κ i (inc σ) : Qbar l) * (cycBar F Ω l (inc σ) : Qbar l) ^ (-m i) := by
        simp [ψ, ε]
      rw [h1, ← hκ, ← hcyc L, Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      congr 1) hV
  obtain ⟨b₀, hb₀⟩ := T
  have h2 := isRoot_of_tri b₀ _ _ (hb₀ (some φ)).1 (hb₀ (some φ)).2 i
  rw [e, wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk]
  have h3 : μ φ i = ((normV w : ℕ) : ℂ) ^ m i * ι ((κ i (Subgroup.inclusion (Weil_le_Dec h) φ) *
      cycBar F Ω l (φ : G F Ω) ^ (-m i) : (Qbar l)ˣ) : Qbar l) := by
    simp only [μ, hφ, mul_one]
    rfl
  obtain ⟨u, -, hu, -, hc, hρ⟩ := wdRep_spec (Loc.PP l) ι Bw h hj ρ
  rw [← h3, (GlobalTheory.WeilDeligne.isFrobSS_of_unipotent u hu hc hρ).charpoly_eq φ]
  exact h2

end GlobalTheory.FlagFrob

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligne_frobenius_eigenvalue_of_full_flag : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ∀ (i : Fin n) (φ : ↥(Weil h)), deg φ = 1 →
        (WD.charPol (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) φ).IsRoot
          (((normV w : ℕ) : ℂ) ^ m i * ι ((κ i (Subgroup.inclusion (Weil_le_Dec h) φ) *
            cycBar F Ω l (φ : G F Ω) ^ (-m i) : (Qbar l)ˣ) : Qbar l)) := by
  first | exact @GlobalTheory.FlagFrob.isRoot_charPol_wdAt | exact GlobalTheory.FlagFrob.isRoot_charPol_wdAt | (intros; apply GlobalTheory.FlagFrob.isRoot_charPol_wdAt <;> assumption)

end
end

