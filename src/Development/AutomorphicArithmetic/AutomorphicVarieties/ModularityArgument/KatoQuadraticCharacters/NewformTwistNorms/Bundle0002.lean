import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0122
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.AutomorphicNewformOfHyp
section
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open scoped Matrix

open private UpperTheory.V.Af.infOf_of_weights UpperTheory.V.Af.exists_over from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
open private UpperTheory.V.Af.NewformAutomorphy.ev_not_mem UpperTheory.V.Af.NewformAutomorphy.normV_eq UpperTheory.V.Af.NewformAutomorphy.scale_charpoly
  UpperTheory.V.Af.NewformAutomorphy.ss_of_tw from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Ord2.AutNewformCopy

open UpperTheory.V UpperTheory.V.Af

private theorem flag_stable {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (D N N' : Subgroup Γ) (hN : N ≤ N')
    (hc : ∀ d ∈ D, ∀ s ∈ N, d⁻¹ * s * d ∈ N) (χ : Fin 2 → Γ →* kˣ) (hne : ∃ s ∈ N, χ 0 s ≠ χ 1 s)
    (h : IsFlagOn r N' fun i => (χ i).comp N'.subtype) :
    ∃ κ, IsFlagOn r D κ ∧ ∀ i (s : ↥D), (s : Γ) ∈ N → κ i s = χ i s := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨s0, hs0, hne⟩ := hne
  let M : Γ →* GL (Fin 2) k := (MulAut.conj g).toMonoidHom.comp r
  have hM : ∀ s, M s = g * r s * g⁻¹ := fun _ => rfl
  have h1 : ∀ s ∈ N, M s 1 0 = 0 := fun s hs => (hg ⟨s, hN hs⟩).1 1 0 (by decide)
  have h2 : ∀ s ∈ N, ∀ i, M s i i = χ i s := fun s hs i => (hg ⟨s, hN hs⟩).2 i
  have hmul : ∀ s t i j, M (s * t) i j = M s i 0 * M t 0 j + M s i 1 * M t 1 j := fun s t i j => by
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : ∀ d ∈ D, M d 1 0 = 0 := fun d hd => by
    have e : s0 * d = d * (d⁻¹ * s0 * d) := by group
    have e2 := hmul s0 d 1 0
    have e3 : χ 0 (d⁻¹ * s0 * d) = χ 0 s0 := by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
    rw [e, hmul, h1 _ (hc d hd s0 hs0), h1 _ hs0, h2 _ (hc d hd s0 hs0), h2 _ hs0, e3] at e2
    have : (χ 0 s0 : k) - χ 1 s0 ≠ 0 := sub_ne_zero.2 fun h => hne (Units.ext h)
    apply mul_left_cancel₀ this
    linear_combination e2
  refine ⟨fun i => MonoidHom.toHomUnits
    { toFun := fun s => M s i i
      map_one' := by simp
      map_mul' := fun s t => by
        rw [Subgroup.coe_mul, hmul]
        fin_cases i
        · simp [h3 _ t.2]
        · simp [h3 _ s.2] }, ⟨g, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩, fun i s hs => Units.ext (h2 _ hs i)⟩
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact h3 _ s.2
  · exact absurd hij (by decide)

private theorem dual_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem det_flag {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (H : Subgroup Γ) (κ : Fin 2 → ↥H →* kˣ)
    (h : IsFlagOn r H κ) (s : ↥H) : Matrix.GeneralLinearGroup.det (r s) = κ 0 s * κ 1 s := by
  obtain ⟨g, hg⟩ := h
  have : Matrix.GeneralLinearGroup.det (r s) = Matrix.GeneralLinearGroup.det (g * r s * g⁻¹) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
  rw [this]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
  simp

private theorem ss_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  refine UpperTheory.V.Af.NewformAutomorphy.ss_of_tw _ χ⁻¹ ?_
  convert h
  ext s : 2
  rw [tw_val, tw_val, smul_smul]
  simp

private theorem place_of {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} [hp : Fact p.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp.out)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have e : v = w := HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
  exact e ▸ hv

private theorem cont_cycBar (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)

private theorem cyc_inf {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun k hk h => ?_⟩
  have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [he, hu.unit_spec, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  omega

private theorem inf_char (P : HypothesesH) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (π : TR.CuspSub ℚ 2) (hreg : π.IsRegAlg) (hatt : AttR ι W π)
    {B : ValuationSubring Ω} (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    (∃ wt HT, Published.IsGalRepOfR π ι W wt HT) ∧ ∀ v, π.HasInfChar v (infOf ![(e : ℤ), -(e : ℤ)]) := by
  have : IsGalois ℚ Ω := {}
  have := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : H.normalCore.Normal := H.normalCore_normal
  have hH' : IsOpen (H.normalCore : Set (G ℚ Ω)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
  have hk : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : ∀ s ∈ Ine (F := ℚ) B, s ^ H.normalCore.index ∈ H.normalCore ⊓ Ine (F := ℚ) B := fun s hs =>
    ⟨@Subgroup.pow_index_mem _ _ _ hn s, Subgroup.pow_mem _ hs _⟩
  have hle : H.normalCore ⊓ Ine (F := ℚ) B ≤ H ⊓ Ine (F := ℚ) B := inf_le_inf_right _ H.normalCore_le
  have halg : IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ (((2 : ℕ) : ℤ) - 1)) := by
    refine (algOfCyc P ℚ Ω l ι).1 _ ?_ fun w hw => ⟨B, place_of hB hw, ((2 : ℕ) : ℤ) - 1, H.normalCore.index,
      Nat.pos_of_ne_zero hk, fun s hs => ?_⟩
    · have h1 : Continuous fun s => Matrix.GeneralLinearGroup.det (W s) * cycBar ℚ Ω l s ^ (((2 : ℕ) : ℤ) - 1) :=
        (Matrix.GeneralLinearGroup.continuous_det.comp hW).mul ((continuous_zpow _).comp (cont_cycBar ℚ Ω l))
      exact h1
    · have h1 := det_flag W _ _ hfl ⟨_, hle (hpow s hs)⟩
      rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one,
        ← map_pow, MonoidHom.comp_apply, h1]
      change cycBar ℚ Ω l _ ^ (e : ℤ) * cycBar ℚ Ω l _ ^ (-(e : ℤ)) = 1
      rw [← zpow_add, add_neg_cancel, zpow_zero]
  obtain ⟨χ, hχ⟩ := halg
  have hsd := (selfDualR P ℚ Ω l ι 2 (by omega) W π hatt _ χ (dual_det W) hχ).1
  obtain ⟨-, wt, HT, -, -, hall⟩ := exR P ℚ Ω l ι 2 (by omega) π χ hreg ⟨fun v v' => by rw [Subsingleton.elim v v'], hsd⟩
  have hG := hall W hW hatt
  refine ⟨⟨wt, HT, hG⟩, fun v => ?_⟩
  obtain ⟨κ, hκ, hI⟩ := flag_stable W (Dec (F := ℚ) B) _ _ hle
    (fun d hd s hs => ⟨hn.conj_mem' s hs.1 d,
      by simpa using conj_mem_Ine ((Dec (F := ℚ) B).inv_mem hd) hs.2⟩)
    (fun i => (cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (by
      obtain ⟨s, hs, h⟩ := cyc_inf hB
      refine ⟨_, hpow s hs, fun h1 => h (H.normalCore.index * (e + e)) (mul_ne_zero hk (by omega)) ?_⟩
      rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, map_pow] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at h1
      rw [pow_mul, pow_add]
      exact mul_eq_one_iff_eq_inv.2 h1) hfl
  obtain ⟨w, hw⟩ := UpperTheory.V.Af.exists_over ℚ l
  have h := place_of hB hw
  obtain ⟨j, L0, hj, hBw⟩ := GlobalTheory.PlaceBridge.exists_locBridge l ℚ Ω w B hw h
  obtain ⟨Bw, hBj, -⟩ := hBw L0 le_rfl
  have hInd : Induces Bw := fun x => by rw [hBj]; exact hj x
  have hJ := (hG.above _ _ (Loc.tiedP l) w B h _ Bw hInd).2.1 (Bw.j.comp (algebraMap ℚ Ω)) Bw.Kw (AlgHom.id _ _)
    fun _ => rfl
  have hH2 := jumpsOpen ![(e : ℤ), -(e : ℤ)] W hW B Bw hInd κ _ hH' hκ hI _ _ hJ
  obtain ⟨μ, hμ, -⟩ := hreg v
  have hW := hG.weights (Bw.j.comp (algebraMap ℚ Ω)) μ (by rwa [Subsingleton.elim (InfinitePlace.mk _) v])
  rw [hH2] at hW
  rwa [UpperTheory.V.Af.infOf_of_weights _ μ hW] at hμ

private theorem charpoly_smul {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have := UpperTheory.V.Af.NewformAutomorphy.scale_charpoly φ (c • M) c⁻¹ (inv_ne_zero hc) (B.map (φ c * ·)) (by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, h, Multiset.map_map]
    simp only [Function.comp_def, map_inv₀, inv_mul_cancel_left₀ hc'])
  rwa [Multiset.map_map] at this

end GlobalTheory.Ord2.AutNewformCopy

open UpperTheory.V UpperTheory.V.Af GlobalTheory.Ord2.AutNewformCopy in

theorem GlobalTheory.Ord2.autNewformOfKnownTheorems :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Published.RepNewform → UpperTheory.V.Pr.AutNewform := by
  rintro P hN Ω _ _ _ l hl ι e he W hW - ⟨π, hreg, hatt⟩ B hB H hH hfl
  obtain ⟨⟨wt, HT, hG⟩, hinf⟩ := inf_char P ι he W hW π hreg hatt hB H hH hfl
  obtain ⟨f, hf⟩ := hN (2 * e + 1) (by omega) e π fun v => by
    convert hinf v using 1
    simp only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, ← Multiset.cons_coe,
      Multiset.coe_nil, Multiset.cons_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    congr 2 <;> push_cast <;> ring
  have hfrob : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∀ B, π.HasSat w B →
      FrobEig ι W w (algSat 2 (normV w) B) := by
    intro w hw B hB
    obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P.toClassicalTheorems ℚ 2 π w
    exact satFrob P.toClassicalTheorems ℚ Ω l ι 2 W hW w hw σ B
      (((satLoc P.toClassicalTheorems ℚ 2 w σ).2 _ π.finPart (hiso σ hσ) B).1 hB) fun A h rc hrc => hG.away w hw A h rc hrc σ hσ
  refine ⟨f, ss_tw _ _ hatt.1, ?_⟩
  filter_upwards [UpperTheory.V.Af.NewformAutomorphy.ev_not_mem l hl.out.ne_zero,
    UpperTheory.V.Af.NewformAutomorphy.ev_not_mem f.M f.pos.ne'] with w hwl hwM A hA
  have hM : ¬ normV w ∣ f.M := by
    rintro ⟨c, hc⟩
    apply hwM
    rw [hc, Nat.cast_mul, UpperTheory.V.Af.NewformAutomorphy.normV_eq]
    exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
  obtain ⟨S, hS, hpoly⟩ := hf w hM
  obtain ⟨h1, h2⟩ := hfrob w hwl S hS A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h3 : cycZ ℚ Ω l s = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp
    apply Units.ext
    rw [tw_val, h1 s hs, MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h3, map_one, one_zpow, Units.val_one, one_smul]
  · have h3 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
    have h4 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ) := by
      rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h3, map_zpow₀,
        map_inv₀, map_natCast, inv_zpow', neg_neg]
    rw [tw_val, charpoly_smul _ _ _ (Units.ne_zero _) _ (h2 σ hσ), h4, hpoly]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.ExistsCuspidalSatakeAtPrimeToLevelOfNewform
section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NewformAutAtL

open Polynomial

private theorem ss_of_tw' {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).2 hW)
  exact ⟨W', (key W').1 hW', hc⟩

private theorem ev_not_mem' (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

private theorem normV_eq' (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

private theorem normV_rat' {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [normV_eq']
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top

private theorem scale_charpoly' {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring

theorem newformAut_atL : Af.Hypotheses₂ → ∀ (e : ℕ) (g : Newform (2 * e + 1)) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)), 1 ≤ e →
    g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M →
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι V π ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∃ B, π.HasSat w B ∧
        ((algSat 2 l B).map fun b => Polynomial.X - Polynomial.C ((l : ℂ) ^ e * b)).prod = g.heckePoly l := by
  intro P e g l hl Ω _ _ _ ι V he hf hlM
  have hk : 2 ≤ 2 * e + 1 := by omega
  obtain ⟨π, hinf, hsat⟩ := P.newform (2 * e + 1) hk g (e : ℤ)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw' _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : ((2 * e + 1 : ℕ) : ℂ) = 1 := by linear_combination h
    have h2 : 2 * e + 1 = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨(e : ℤ), by push_cast; ring⟩
    · exact ⟨1 - ((2 * e + 1 : ℕ) : ℤ) + e, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem' l hl.out.ne_zero, ev_not_mem' g.M g.pos.ne'] with w hw hwl hwM
    have hM : ¬ normV w ∣ g.M := by
      rintro ⟨c, hc⟩
      apply hwM
      rw [hc, Nat.cast_mul, normV_eq']
      exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
    obtain ⟨B, hB, hpoly⟩ := hsat w hM
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ (-(e : ℤ))) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly' ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow', neg_neg]
      rw [h3]
  · intro w hw
    have hn : normV w = l := normV_rat' hl.out w hw
    have hM : ¬ normV w ∣ g.M := hn ▸ hlM
    obtain ⟨B, hB, hpoly⟩ := hsat w hM
    refine ⟨B, hB, ?_⟩
    rw [hn] at hpoly
    simpa only [zpow_natCast] using hpoly

end GlobalTheory.NewformAutAtL

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidal_satake_at_prime_to_level_of_newform : Af.Hypotheses₂ → ∀ (e : ℕ) (g : Newform (2 * e + 1)) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)), 1 ≤ e →
    g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M →
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι V π ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∃ B, π.HasSat w B ∧
        ((algSat 2 l B).map fun b => Polynomial.X - Polynomial.C ((l : ℂ) ^ e * b)).prod = g.heckePoly l := by
  first | exact @GlobalTheory.NewformAutAtL.newformAut_atL | exact GlobalTheory.NewformAutAtL.newformAut_atL | (intros; apply GlobalTheory.NewformAutAtL.newformAut_atL <;> assumption)

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.LocalMemPrincipalCongruence
section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Ord2.LevelOfOrd

theorem asIdeal_eq_span (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
  have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
    exact Nat.prime_iff_prime_int.1 Fact.out
  exact ((((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal
    (mt Ideal.span_singleton_eq_bot.1 hp.ne_zero)).eq_of_le v.isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).2 h)).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e M : ℕ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    1 ≤ e → 1 ≤ M → Continuous V → LevelAway l M V → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ →
    (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) →
    Level l M ![(e : ℤ), -(e : ℤ)] V := by
  intro l _ Ω _ _ _ e M V A κ he _ hcont haway hA hflag hine
  obtain ⟨v, hvA, hlv⟩ := hA
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hvA ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  let m : Fin 2 → ℤ := ![(e : ℤ), -(e : ℤ)]
  have hm : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ i s = cycBar ℚ Ω l s ^ m i := by
    intro i s hs
    fin_cases i
    · exact (hine s hs).1
    · exact (hine s hs).2
  refine ⟨hcont, haway, ?_⟩
  intro w hw
  have hwv : w = v := HeightOneSpectrum.ext ((asIdeal_eq_span l w hw).trans (asIdeal_eq_span l v hlv).symm)
  subst hwv
  refine ⟨A, hvA, fun _ => 1, κ, fun i s _ => rfl, hflag, fun i s hs => by rw [hm i s hs]; exact (mul_one _).symm, Or.inl ?_⟩
  intro i j h
  have hn : m i - m j - 1 ≠ 0 := by
    have : (1 : ℤ) ≤ e := by exact_mod_cast he
    fin_cases i <;> fin_cases j <;> simp [m] <;> omega
  obtain ⟨g, hg, hgn⟩ := UpperTheory.V.Ws.Pt.cycIne ℚ Ω l A hval _ hn
  apply hgn
  have hD : g ∈ Dec (F := ℚ) A := Ine_le_Dec A hg
  have h1 := DFunLike.congr_fun h ⟨g, hD⟩
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hm i ⟨g, hD⟩ hg, hm j ⟨g, hD⟩ hg] at h1
  change cycBar ℚ Ω l g ^ m i = cycBar ℚ Ω l g ^ m j * cycBar ℚ Ω l g at h1
  rw [sub_sub, zpow_sub, zpow_add_one, ← h1, mul_inv_cancel]

end GlobalTheory.Ord2.LevelOfOrd

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_flag_inertia_weights : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e M : ℕ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    1 ≤ e → 1 ≤ M → Continuous V → LevelAway l M V → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ →
    (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) →
    Level l M ![(e : ℤ), -(e : ℤ)] V := by
  first | exact @GlobalTheory.Ord2.LevelOfOrd.main | exact GlobalTheory.Ord2.LevelOfOrd.main | (intros; apply GlobalTheory.Ord2.LevelOfOrd.main <;> assumption)

end
end

