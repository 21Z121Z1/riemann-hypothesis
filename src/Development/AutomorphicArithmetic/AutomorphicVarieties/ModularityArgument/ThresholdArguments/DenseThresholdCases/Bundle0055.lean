import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.LocDataT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.ZEqDimE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0052
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocDataT
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.Zero.LLC
open GlobalTheory.PRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open private rel_of_chars chi_unit from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LLocData
open private charpoly_smul_prod absPow_neg_nat from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.NuChar
namespace UpperTheory.V.Z.Win.LocalCharacterData
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
private theorem psi_val (ψ : Fin n → kˣ →* ℂˣ) (χ : (Fin n → kˣ) →* ℂˣ)
    (hχ : torusChar ψ = χ * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom))
    (x : kˣ) (i : Fin n) :
    (ψ i x : ℂ) = (resCard k : ℂ) ^ (((i : ℕ) : ℤ) * ord k x) * χ (Pi.mulSingle i x) * (absPow k (((n : ℂ) - 1) / 2) x : ℂ) := by
  have h1 : torusChar ψ (Pi.mulSingle i x) = ψ i x := by
    rw [torusChar_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  have hd : ∀ (t : Fin n → kˣ) j, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t j) = t j := fun t =>
    congrFun ((leviTorus k (Fin n)).left_inv t)
  have h2 : deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (Pi.mulSingle i x)) =
      absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) x := by
    rw [deltaHalf_apply, Finset.prod_eq_single i, hd, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [hd, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  have h3 : (modExp (fun _ : Fin n => Unit) i : ℂ) / 2 = -((i : ℕ) : ℂ) + ((n : ℂ) - 1) / 2 := by
    rw [modExp_fin _ (fun _ => by simp)]
    push_cast
    ring
  have h4 := absPow_neg_nat k (i : ℕ) x
  rw [← h1, hχ]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
  erw [h2]
  rw [h3, absPow_add, MonoidHom.mul_apply, Units.val_mul, h4]
  ring
private theorem unlinked_of_gen (ψ : Fin n → kˣ →* ℂˣ) (hψ : ∀ i, IsSmoothChar (ψ i)) (χ : (Fin n → kˣ) →* ℂˣ)
    (hχ : torusChar ψ = χ * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom))
    (x : kˣ) (hx : ord k x = 1) (α : Fin n → ℂ)
    (hα : ∀ i, α i = (resCard k : ℂ) ^ (i : ℕ) * χ (Pi.mulSingle i x))
    (hgen : ∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (resCard k : ℂ) * α i') :
    GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ψ hψ) := by
  have hq2 : 2 ≤ resCard k := Finite.one_lt_card (α := 𝓀[k])
  have hq0 : (resCard k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hq1 : (resCard k : ℂ) ≠ 1 := fun e => by
    have : resCard k = 1 := by exact_mod_cast e
    omega
  have hab : (absPow k 1 x : ℂ) * (resCard k : ℂ) = 1 := by
    rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, hx, Complex.cpow_one]
    simp [hq0]
  intro y hy z hz e
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
  have e1 : (ψ i x : ℂ) = ψ j x * (absPow k ((1 : ℂ)) x : ℂ) := by
    rw [e]
    simp
  rw [psi_val ψ χ hχ x i, psi_val ψ χ hχ x j, hx, mul_one, mul_one, zpow_natCast, zpow_natCast, ← hα, ← hα] at e1
  have hu : (absPow k (((n : ℂ) - 1) / 2) x : ℂ) ≠ 0 := Units.ne_zero _
  have e2 : α i = α j * (absPow k ((1 : ℂ)) x : ℂ) := by
    apply mul_right_cancel₀ hu
    rw [e1]
    ring
  have e3 : α j = (resCard k : ℂ) * α i := by
    rw [e2]
    linear_combination (-α j) * hab
  have hne : α i ≠ 0 := by
    rw [hα]
    exact mul_ne_zero (pow_ne_zero _ hq0) (Units.ne_zero _)
  by_cases hij : j = i
  · subst hij
    have : (1 : ℂ) = resCard k := mul_right_cancel₀ hne ((one_mul _).trans e3)
    exact hq1 this.symm
  · exact (hgen j i hij).2 e3
end Loc
end UpperTheory.V.Z.Win.LocalCharacterData
namespace UpperTheory.V.Z.Win.LocalCharacterData
section WD
open Polynomial
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (w.adicCompletion E) → WD h} {n : ℕ}
private theorem support_chars (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hψ : ∀ i, IsSmoothChar (ψ i)) (hs : IsSubquotient σ.ρ (prinSeries ψ)) :
    HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (GlobalTheory.RoadU.chars ψ hψ) :=
  (hasSupport_of_isCuspSupport (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries (k := w.adicCompletion E)
    ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ hψ hs)).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
private theorem jqRecV (L : LawsV a ha ε rc) (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (hψ : ∀ i, IsSmoothChar (ψ i)) (hs : IsSubquotient σ.ρ (prinSeries ψ))
    (g : Weil h) :
    (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol g = ∏ i, (X - C ((ψ i (a g) : ℂˣ) : ℂ)) := by
  rw [L.supp _ _ (support_chars σ ψ hψ hs) g, GlobalTheory.RoadU.chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [L.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp
private theorem nuCharV (L : LawsV a ha ε rc) (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (χ : (Fin n → (w.adicCompletion E)ˣ) →* ℂˣ) (hψ : ∀ i, IsSmoothChar (ψ i))
    (hχ : torusChar ψ = χ * ((deltaHalf (w.adicCompletion E) fun _ : Fin n => Unit).comp
      (leviTorus (w.adicCompletion E) (Fin n)).toMonoidHom))
    (hs : IsSubquotient σ.ρ (prinSeries ψ)) (g : Weil h) :
    (rc (algNorm σ)).charPol g = ∏ i : Fin n, (X - C ((resCard (w.adicCompletion E) : ℂ) ^
      (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) * (χ (Pi.mulSingle i (a g)) : ℂ))) := by
  have H := jqRecV L σ ψ hψ hs g
  rw [algNorm, L.nu_eq]
  generalize rc (IrrGL.of σ.ρ σ.smooth σ.irred) = x at H ⊢
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.charPol_mk] at H
  rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, ← GlobalTheory.SatChar.absPow_art ha ((1 - (n : ℝ)) / 2) g,
    charpoly_smul_prod _ _ (Units.ne_zero _) _ H]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  have e1 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  have e2 : (absPow (w.adicCompletion E) (((n : ℂ) - 1) / 2) (a g) : ℂ) *
      (absPow (w.adicCompletion E) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) (a g) : ℂ) = 1 := by
    rw [← Units.val_mul, ← MonoidHom.mul_apply, ← absPow_add, e1, val_absPow, Complex.cpow_zero]
  rw [psi_val ψ χ hχ (a g) i]
  linear_combination ((resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) *
    (χ (Pi.mulSingle i (a g)) : ℂ)) * e2
end WD
end UpperTheory.V.Z.Win.LocalCharacterData
open UpperTheory.V.Z.Win.LocalCharacterData in
theorem UpperTheory.V.Z.Win.locDataT_alt :
    _root_.UpperTheory.V.Z.Win.LocDataTAlt := by
  intro hP l _ E Ω _ _ _ _ _ Bq w hB hl fr τ hfr hF hτ
  obtain ⟨rc, hrc⟩ := recTExists E Ω Bq w hB
  obtain ⟨a, ha, ε, L⟩ := UpperTheory.V.Z.Win.extraV E Ω Bq w hB rc hrc
  obtain ⟨hq, h1, h2, hx, hδ, hk, hrel⟩ := artinEl hP.tame l E Ω Bq w hB hl a ha fr τ hfr hF hτ
  refine ⟨hq, _, _, hx, hδ, fun n ι r σ H C hC θ hθ χ hχ α hα => ?_⟩
  obtain ⟨ψ, hψ, hψC, hψχ, hsub⟩ := jqEmbed hP.bz _ n C σ.V σ.ρ σ.smooth σ.irred θ hθ χ hχ
  have hν := nuCharV L σ ψ χ hψ hψχ hsub
  have hord1 : ord (w.adicCompletion E) (a ⟨fr, h1⟩) = 1 := by
    have h2 : deg (⟨fr, h1⟩ : Weil hB)⁻¹ = 1 := deg_eq_one_iff.2 hF
    rw [ha.ord_eq, ← deg_inv, h2]
  have hgen : (∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (resCard (w.adicCompletion E) : ℂ) * α i') →
      UpperTheory.V.Z.Win.Gd (rc (algNorm σ)) := fun hg =>
    UpperTheory.V.Z.Win.Gu.plainGd E Ω Bq w hB rc hrc n σ ⟨_, support_chars σ ψ hψ hsub, fun y hy => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
      rfl, unlinked_of_gen ψ hψ χ hψχ _ hord1 α hα hg⟩
  have hsph : IsSpherical σ.ρ → UpperTheory.V.Z.Win.Gd (rc (algNorm σ)) := fun hs => by
    have G := UpperTheory.V.Z.Win.Gu.gdLaws E Ω Bq w hB
    rw [algNorm, L.nu_eq]
    exact (G.2.1 _ _).2 (G.2.2.2 _ ((L.sph _).1 (fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) hs)))
  have core : UpperTheory.V.Z.Win.Gd (rc (algNorm σ)) →
      (((r fr : Matrix (Fin n) (Fin n) (Qbar l)).map ι).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) ∧
      ((∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (resCard (w.adicCompletion E) : ℂ) * α i') → ∀ i,
        (List.ofFn fun i' => if i' = i then 1 else
          ((r fr : Matrix (Fin n) (Fin n) (Qbar l)).map ι) - α i' • (1 : Matrix (Fin n) (Fin n) ℂ)).prod *
        (((r τ : Matrix (Fin n) (Fin n) (Qbar l)).map ι) -
          (χ (Pi.mulSingle i (a ⟨τ, h2⟩)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0) := fun hgd => by
    have hx0 := (H rc hrc).isWDOf hgd
    obtain ⟨hw1, hw2⟩ := wdChar l E Ω Bq w hB hl n ι r _ hx0
    have hq2 : 2 ≤ resCard (w.adicCompletion E) := Finite.one_lt_card (α := 𝓀[w.adicCompletion E])
    have hq0 : (resCard (w.adicCompletion E) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    let c : Fin n → Weil hB →* ℂ := fun i =>
      { toFun := fun g => (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) *
          (χ (Pi.mulSingle i (a g)) : ℂ)
        map_one' := by
          rw [map_one, Pi.mulSingle_one, map_one, ord_eq_zero (by simp)]
          simp
        map_mul' := fun g g' => by
          rw [map_mul, ord_mul, Pi.mulSingle_mul, map_mul, mul_add, zpow_add₀ hq0, Units.val_mul]
          ring }
    let R : Weil hB →* GL (Fin n) ℂ :=
      ((Matrix.GeneralLinearGroup.map ι.toRingHom).comp r).comp (Weil hB).subtype
    have hR : ∀ g, (R g : Matrix (Fin n) (Fin n) ℂ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (c i g)) :=
      fun g => (hw1 g).trans (hν g)
    have hord : ∀ g : Weil hB, (g : G E Ω) ∈ Ine (F := E) Bq → ord (w.adicCompletion E) (a g) = 0 := fun g hg => by
      rw [ha.ord_eq, deg_eq_zero_iff.2 hg, neg_zero]
    have hf : ∀ i, α i = c i ⟨fr, h1⟩ := fun i => by
      rw [hα]
      change _ = (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a ⟨fr, h1⟩)) * _
      rw [hord1, mul_one, zpow_natCast]
    have ht : ∀ i, (χ (Pi.mulSingle i (a ⟨τ, h2⟩)) : ℂ) = c i ⟨τ, h2⟩ := fun i => by
      change _ = (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a ⟨τ, h2⟩)) * _
      rw [hord _ hτ.1, mul_zero, zpow_zero, one_mul]
    have hαc : α = fun i => c i ⟨fr, h1⟩ := funext hf
    refine ⟨hαc ▸ hR ⟨fr, h1⟩, fun hg i => ?_⟩
    rw [ht]
    rw [hαc] at hg ⊢
    set g : Weil hB := ((⟨τ, h2⟩ : Weil hB) ^ resCard (w.adicCompletion E))⁻¹ *
      ((⟨fr, h1⟩ : Weil hB)⁻¹ * ⟨τ, h2⟩ * ⟨fr, h1⟩) with hg'
    have hgk : (g : G E Ω) ∈ GlobalTheory.TameQuot.ineKer E Bq l := by
      rw [← hq] at hrel
      exact hrel
    have hcg : ∀ i, c i g = 1 := fun i => by
      have e := hord g (GlobalTheory.TameQuot.ineKer_le_Ine Bq l hgk)
      have e2 : a g ∈ unitsC _ C := Subgroup.map_mono (Subgroup.comap_mono hC) (hk g g.2 hgk)
      change (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) *
        (χ (Pi.mulSingle i (a g)) : ℂ) = 1
      rw [e, chi_unit ψ χ hψχ i _ e (hψC i _ e2)]
      simp
    have hRg : R g = 1 := by
      have e : r g = 1 := hw2 g hgk (((hw1 g).trans (hν g)).trans (by
        change ∏ i, (Polynomial.X - Polynomial.C (c i g)) = _
        simp [hcg]))
      change Matrix.GeneralLinearGroup.map ι.toRingHom (r g) = 1
      rw [e, map_one]
    exact rel_of_chars hq2 R c hR ⟨fr, h1⟩ ⟨τ, h2⟩ hRg hcg hg i
  exact ⟨fun hc => (core (hc.elim hsph hgen)).1, fun hg => (core (hgen hg)).2 hg⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TZEqDimE
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

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
open private au_isTeich from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.Desc.V0
private theorem ePart_zero {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ 0 0 = ⊤ := by
  simp [ePart, opE]
private theorem card_not_dvd {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (j : ℕ) : ¬ l ∣ Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j := by
  have hl : l.Prime := Fact.out
  have hw : (s.w s.v0).under (𝓞 (Lp L)) = s.v0 := by
    ext x
    exact (s.hw s.v0 (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA s.v0 x)
  have h2 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← s.norm_v0_eq_one, normV, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have h3 : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← hw] at h2
    have h4 : algebraMap (𝓞 (Lp L)) (𝓞 L) ((s.p : ℕ) : 𝓞 (Lp L)) ∈ (s.w s.v0).asIdeal := h2
    rwa [map_natCast] at h4
  have hd : Ideal.absNorm (s.w s.v0).asIdeal ∣ Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h3)
  have hn : Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) = s.p ^ Module.finrank ℤ (𝓞 L) := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)), Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  rw [hn] at hd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow s.p_prime).1 hd
  have hq : Nat.card 𝓀[(s.w s.v0).adicCompletion L] = s.p ^ e := (resCard_eq_normV _).trans he
  intro h
  rw [hq] at h
  exact s.p_ne ((Nat.prime_dvd_prime_iff_eq hl s.p_prime).1 (hl.dvd_of_dvd_pow (hl.dvd_of_dvd_pow h))).symm
set_option maxHeartbeats 1600000 in
theorem z_eq_dim_e_of_count_e_res_eq_inv_loc_kir : _root_.UpperTheory.V.Z.Desc.V0.CountEAlt → _root_.UpperTheory.V.Z.J.D.ResidualEqualityRankTwo → InvEq1 → InvBox → LocE → KirCusp → _root_.UpperTheory.V.Z.Desc.V0.ZEqDimEAlt := by
  intro hCount hRes hInv hBox hLoc hKir hP hM hC l _ L Ω _ _ _ _ _ _ s n hn V hV hn4
  obtain ⟨a, j, D₀, hE, hD₀, hdim⟩ := hLoc ((s.w s.v0).adicCompletion L) n
  refine ⟨a, Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j, hE, card_not_dvd s j, ?_⟩
  intro Q c r ι m τ₀ hτ A _ _ _ θ hθ lam K D D' h h'
  obtain ⟨a₀, ha⟩ := hCount hP hM hC l L Ω s n hn V hV hn4 ι lam
  obtain ⟨t, ht⟩ := au_isTeich c r
  obtain ⟨χ, hχ, hext⟩ : ∃ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ ∧
      ∀ (u : s.St) (i : Fin n), ∃ ψ : Weil (s.hw u) →* ℂˣ, ∀ g, ψ (ineIncl (s.hw u) g) = χ u i g :=
    ⟨_, hτ t ht, fun u i => ⟨W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l)))
      ((t i).comp (V.pr.comp (Weil (s.hw u)).subtype)), fun _ => rfl⟩⟩
  have key : ∀ D : ℕ, _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt (hset Q τ₀) θ ι lam K (sec0 n s) a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) D →
      ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧
        (∀ (u : s.St) rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (C.u u)))) ∧
        (D : Cardinal) = a₀ * (Module.rank ℂ (cInv1 C ι τ₀) * D₀) ∧ 1 ≤ D := by
    rintro _ ⟨x, d, ξ, c0, sp, ev, hs, hu, hz, hall, rfl⟩
    obtain ⟨e, he⟩ := hs.alg
    obtain ⟨π, σ, C, h1, h2, h3, h4, h5⟩ := ha Q c r m τ₀ hτ d e ξ he A θ x c0 sp hθ hs K ev hu hz hall
    haveI : FiniteDimensional ℂ (zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) :=
      haveI := hs.fin K c0 le_rfl
      Submodule.finiteDimensional_of_le (S₂ := (hset Q τ₀).ClAt θ ι x.toRingHom lam ξ K c0)
        (inf_le_left.trans (iSup_le fun _ => inf_le_left))
    have hb := fun (a' : GLw n (s.w s.v0) →₀ ℤ) (N' : ℕ) => hBox _ _ _ _ (piRep fun u => (C.u u).ρ) C.o.ρ m (KT n (wt s)) (Kc _ n 1)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) a' N'
    have h0 := h5 0 0 (by simp)
    have hz0 : Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) ≠ 0 :=
      fun hf => hz (Submodule.finrank_eq_zero.1 hf)
    rw [show eC Q τ₀ d 0 0 = ⊤ from ePart_zero _, inf_top_eq, hb 0 0, ePart_zero, inf_top_eq] at h0
    have hne : (a₀ : Cardinal) * (Module.rank ℂ (cInv1 C ι τ₀) * Module.rank ℂ ↥(fixd C.o.ρ (Kc _ n 1))) ≠ 0 :=
      h0 ▸ Nat.cast_ne_zero.2 hz0
    have ha₀ : (a₀ : Cardinal) ≠ 0 := left_ne_zero_of_mul hne
    have hr : Module.rank ℂ (cInv1 C ι τ₀) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
    have hf : fixd C.o.ρ (Kc _ n 1) ≠ ⊥ := fun hf => right_ne_zero_of_mul (right_ne_zero_of_mul hne) (by rw [hf]; simp)
    have hd := hdim _ C.o.ρ C.o.smooth (hKir L n hn π (s.w s.v0) C.o h2) hf
    have hD := h5 a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) hE.supp
    rw [hb, hd] at hD
    refine ⟨π, σ, C, h1, fun u rc hrc =>
      _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ h4 h3 χ hχ C.u C.hu u rc hrc, hD, ?_⟩
    refine Nat.one_le_iff_ne_zero.2 fun h0' => ?_
    rw [h0', Nat.cast_zero] at hD
    exact mul_ne_zero ha₀ (mul_ne_zero hr (Nat.cast_ne_zero.2 hD₀.ne')) hD.symm
  obtain ⟨π, σ, C, a1, a3, a5, a6⟩ := key D h
  obtain ⟨π', σ', C', b1, b3, b5, -⟩ := key D' h'
  have hr : Module.rank ℂ (cInv1 C ι τ₀) = Module.rank ℂ (cInv1 C' ι τ₀) :=
    hInv l L Ω s n hn V hV c ι m τ₀ σ σ' C C'
      (fun u => hRes hP.litN L Ω n hn π π' (s.w u) (s.A u) (s.hw u) (C.u u) (C'.u u) (a1 u) (b1 u) (χ u) (hext u) (a3 u) (b3 u))
  rw [hr, ← b5] at a5
  exact ⟨a6, Nat.cast_injective (R := Cardinal) a5⟩
end UpperTheory.V.Z.Desc.V0
end
end
end

