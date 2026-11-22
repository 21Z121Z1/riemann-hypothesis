import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolume
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormNonzeroAtOneLift
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LiftInterp

theorem zero_mem_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) : (0 : Frame X.Ψ r → ℂ) ∈ X.SS la := by
  obtain ⟨⟨hz, -, -⟩, -⟩ := siegelSpaceAlgebra_holds r X la la 0
  exact hz

theorem bchar_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (la : Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  classical
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  intro h0
  apply (hb τ).1
  have hU : (mat b τ).IsUpperTriangular := fun a c hca => (hb τ).2 a c hca
  rw [Matrix.det_of_upperTriangular hU]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [mat] using h0)

theorem comp_interp {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (hχ : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) (G : Subgroup (GL (Fin r) E)) (g : ℕ)
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g) (hgr : 3 * r < g) (hΓG : X.Γ ≤ G)
    (hL' : ∀ γ ∈ G, IsUStab X.Gm X.L' γ) (hΛ : ∀ γ ∈ G, IsUStab X.Gm X.Λ γ)
    (hU : ∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) (s : ℕ) (hs : Even s)
    (hsb : 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) (hNC : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x) :
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x) = 0 := by
  by_cases hdef : X.p0 = 0 ∨ X.p0 = r
  · have h1 := GlobalTheory.T.upperLevel_trivial_definite_noContraction E r X G g hg hgr hL' hU hdef x hx hNC
    obtain ⟨P, hP, hP0⟩ := GlobalTheory.T.exists_detPowerSection_ne_zero_definite E r X.toData (fun γ hγ => h1 γ (hΓG hγ)) hdef s x hx
    refine ⟨P, hP, hP0, fun γ hγ hγ' => absurd ?_ hγ'⟩
    rw [h1 γ hγ]
    exact X.Γ.one_mem
  · push_neg at hdef
    have hp0 : 0 < X.p0 := Nat.pos_of_ne_zero hdef.1
    have hp1 : X.p0 < r := lt_of_le_of_ne X.p0_le hdef.2
    obtain ⟨x0, h0, ⟨b, hb, rfl⟩, hFB⟩ := GlobalTheory.T.freeBall_noContraction_unitaryUpperLevel E r X G g hg hgr hΓG hL' hΛ hU x hx hNC
    obtain ⟨P, hP, hP0, hPγ⟩ := GlobalTheory.T.orbitInterpolation_detWeight_freeBall_indefinite E r X.toData hχ G x0 h0 hFB hp0 hp1 s hs hsb
    have hx0 : x0 ∈ X.dom := IW.orth_mem_dom X.toData x0 h0
    refine ⟨P, hP, ?_, fun γ hγ hγ' => ?_⟩
    · rw [hP.1.1.2.1 x0 hx0 b hb]
      exact mul_ne_zero (bchar_ne_zero _ hb) hP0
    · have hy : lact γ x0 ∈ X.dom := GlobalTheory.MajInv.lact_mem_dom X.toData (hΛ γ hγ) hx0
      rw [FundSetPf.lact_rmul, hP.1.1.2.1 _ hy b hb, hPγ γ hγ hγ', mul_zero]

theorem castFrame_symm_cast {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (y : Frame Ψ r) : castFrame h.symm (castFrame h y) = y := by
  subst h; rfl

theorem castFrame_lact {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (γ : GL (Fin r) E) (y : Frame Ψ r) : castFrame h (lact γ y) = lact γ (castFrame h y) := by
  subst h; rfl

theorem castFrame_mem_GG {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (G : Matrix (Fin r) (Fin r) E) (p : ℕ) (y : Frame Ψ' r) (hy : y ∈ GG Ψ' G p) :
    castFrame h.symm y ∈ GG Ψ G p := by
  subst h; exact hy

theorem castWt_deMul {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (p s : ℕ) :
    castWt h (deMul Ψ' r p s) = deMul Ψ r p s := by
  subst h; rfl

theorem exists_form_one_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s → ∀ (c : C) (x : Frame M.Ψ r), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) (castFrame (M.comp_Ψ c).symm x) → x ∈ M.dom → ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c x ≠ 0 ∧ (∀ h : U, h ≠ 1 → M.pull h u c x = 0) ∧ ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := by
  intro E _ _ _ r U C _ _ _ _ M hLH s hs hsb c x hNC hx
  classical
  obtain ⟨g, hg, hgr, hUn⟩ := GlobalTheory.T.exists_totallySplitPrime_upperLevel_unipotent E r U C M hLH
  obtain ⟨G, hG, hΓG⟩ := GlobalTheory.T.exists_upperLevel_subgroup_component E r U C M c
  have hΨ : (M.comp c).Ψ = M.Ψ := M.comp_Ψ c
  have hx' : castFrame hΨ.symm x ∈ (M.comp c).dom := by
    have := castFrame_mem_GG hΨ M.Gm M.p0 x hx
    show castFrame hΨ.symm x ∈ GG (M.comp c).Ψ (M.comp c).Gm (M.comp c).p0
    rw [M.comp_Gm c, M.comp_basePoint c]
    exact this
  have hsb' : 2 * r + 50 * r ^ 2 * ((M.comp c).Ψ.card * ((M.comp c).p0 * (r - (M.comp c).p0))) + 1 ≤ s := by
    rw [hΨ, M.comp_basePoint c]; exact hsb
  obtain ⟨P, hP, hP0, hPγ⟩ := comp_interp (M.comp c) (M.χ_one c) G g hg hgr hΓG
    (fun β hβ => (GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices E r U C M c β ((hG β).1 hβ)).1) (fun β hβ => (GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices E r U C M c β ((hG β).1 hβ)).2)
    (fun β hβ => hUn c β ((hG β).1 hβ)) s hs hsb' _ hx' hNC
  let u : C → Frame M.Ψ r → ℂ := fun c' y => if c' = c then P (castFrame hΨ.symm y) else 0
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · intro c'
    by_cases hc : c' = c
    · subst hc
      have e : (fun y => u c' (castFrame (M.comp_Ψ c') y)) = P := by
        funext y
        simp only [u, if_pos rfl]
        exact congrArg P (castFrame_symm_cast _ y)
      rw [e, castWt_deMul]
      rw [M.comp_basePoint c'] at hP
      exact hP
    · have e : (fun y => u c' (castFrame (M.comp_Ψ c') y)) = 0 := by
        funext y
        simp [u, hc]
      rw [e]
      exact zero_mem_SS _ _
  · simpa [u] using hP0
  · intro h hh
    unfold TwoLevels.pull
    by_cases hc : h • c = c
    · simp only [u, hc, if_pos rfl]
      rw [castFrame_lact]
      refine hPγ _ ((hG _).2 ⟨h, hc, 1, (M.comp c).Γ.one_mem, by simp⟩) fun hm => hh ?_
      exact M.tr_faithful h c hc hm
    · simp [u, hc]
  · intro c' hc' y
    have hne : c' ≠ c := fun e => hc' 1 (by simp [e])
    simp [u, hne]

end GlobalTheory.LiftInterp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbeddingStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∃ c', CUnit c' ∧ EqAt T R κ (O i) σ hV c' := by
  first | exact @GlobalTheory.EquivConst.exists_equivariant_constants | exact GlobalTheory.EquivConst.exists_equivariant_constants | (intros; apply GlobalTheory.EquivConst.exists_equivariant_constants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariantsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_degree_dvd_card_invariants : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G], Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k), ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧ Module.finrank k K' ∣ Nat.card G ∧ β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  first | exact @GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | exact GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | (intros; apply GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetResidueLogBound
section
open NumberField IsDedekindDomain GlobalTheory.ShFam.Pad

namespace GlobalTheory.PlaceSum

variable {F : Type} [Field F] [NumberField F]

theorem residueCharacteristic_eq_iff (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime) :
    resP v = p ↔ ((p : 𝓞 F) ∈ v.asIdeal) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  unfold resP
  constructor
  · intro h
    have h0 : ((ringChar (𝓞 F ⧸ v.asIdeal) : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := ringChar.Nat.cast_ringChar
    rw [h, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  · intro h
    have h0 : (Ideal.Quotient.mk v.asIdeal (p : 𝓞 F)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
    rw [map_natCast] at h0
    have hd : ringChar (𝓞 F ⧸ v.asIdeal) ∣ p := ringChar.dvd h0
    rcases (Nat.dvd_prime hp).1 hd with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one (R := 𝓞 F ⧸ v.asIdeal))
    · exact h1

theorem finprod_adicAbv {z : F} (hz : z ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v z).Finite ∧
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicAbv F v z =
      |((Algebra.norm ℚ z : ℚ) : ℝ)|⁻¹ := by
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v z) =
      (fun w : FinitePlace F => w z) ∘ FinitePlace.equivHeightOneSpectrum.symm := by
    funext v
    simp [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  refine ⟨?_, ?_⟩
  · rw [hfun, Function.mulSupport_comp_eq_preimage]
    exact (FinitePlace.hasFiniteMulSupport hz).preimage
      FinitePlace.equivHeightOneSpectrum.symm.injective.injOn
  · rw [hfun]
    refine (finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm
      (f := fun w : FinitePlace F => w z)).trans ?_
    rw [FinitePlace.prod_eq_inv_abs_norm hz]
    push_cast; rfl

theorem adicAbv_natCast_ne_one_iff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    HeightOneSpectrum.adicAbv F v (n : F) ≠ 1 ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  have e : (n : F) = algebraMap (𝓞 F) F (n : 𝓞 F) := (map_natCast _ n).symm
  rw [e, Ne, ← not_not (a := (n : 𝓞 F) ∈ v.asIdeal)]
  exact not_congr (v.adicAbv_coe_eq_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _)

theorem finite_mulSupport_adicAbv_natCast {p : ℕ} (hp : p.Prime) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v (p : F)).Finite :=
  (finprod_adicAbv (z := (p : F)) (by exact_mod_cast hp.ne_zero)).1

theorem mem_finite_residueChar_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ (finite_mulSupport_adicAbv_natCast (F := F) hp).toFinset ↔ resP v = p := by
  rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, adicAbv_natCast_ne_one_iff, residueCharacteristic_eq_iff v hp]

theorem sum_localDeg_eq {p : ℕ} (hp : p.Prime) :
    ∑ v ∈ (finite_mulSupport_adicAbv_natCast (F := F) hp).toFinset,
      -Real.log (HeightOneSpectrum.adicAbv F v (p : F)) / Real.log p = (Module.finrank ℚ F : ℝ) := by
  have hp0 : (p : F) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hfin, hprod⟩ := finprod_adicAbv (F := F) hp0
  rw [finprod_eq_prod _ hfin] at hprod
  have hN : Algebra.norm ℚ (p : F) = (p : ℚ) ^ Module.finrank ℚ F := by
    rw [← map_natCast (algebraMap ℚ F) p, Algebra.norm_algebraMap]
  rw [hN] at hprod
  push_cast at hprod
  have hne : ∀ v ∈ hfin.toFinset, HeightOneSpectrum.adicAbv F v (p : F) ≠ 0 :=
    fun v _ => (AbsoluteValue.ne_zero_iff _).2 hp0
  have hlog := congrArg Real.log hprod
  rw [Real.log_prod hne, abs_of_nonneg (by positivity), Real.log_inv, Real.log_pow] at hlog
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [← Finset.sum_div, Finset.sum_neg_distrib, hlog, neg_neg, mul_div_assoc, div_self hlp.ne', mul_one]

theorem sum_localDeg_le : ∀ {F : Type} [Field F] [NumberField F] (T : Finset ℕ), (∀ p ∈ T, p.Prime) →
    ∀ (g : ℕ → ℝ), (∀ p, 0 ≤ g p) →
    (∀ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v (resP v : F) ≤ 1) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∈ S ↔ resP v ∈ T) ∧
      ∑ v ∈ S, (-Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) * g (resP v) ≤
        (Module.finrank ℚ F : ℝ) * ∑ p ∈ T, g p := by
  intro F _ _ T hT g _
  classical
  refine ⟨fun v => HeightOneSpectrum.adicAbv_natCast_le_one F v _, ?_⟩
  let Sp : ℕ → Finset (HeightOneSpectrum (𝓞 F)) := fun p =>
    if h : p.Prime then (finite_mulSupport_adicAbv_natCast (F := F) h).toFinset else ∅
  have hSp : ∀ p ∈ T, ∀ v, v ∈ Sp p ↔ resP v = p := by
    intro p hpT v
    simp only [Sp, dif_pos (hT p hpT)]
    exact mem_finite_residueChar_eq (hT p hpT) v
  let S := T.biUnion Sp
  have hS : ∀ v, v ∈ S ↔ resP v ∈ T := by
    intro v
    simp only [S, Finset.mem_biUnion]
    constructor
    · rintro ⟨p, hpT, hv⟩
      rw [(hSp p hpT v).1 hv]; exact hpT
    · intro h
      exact ⟨resP v, h, (hSp _ h v).2 rfl⟩
  refine ⟨S, hS, le_of_eq ?_⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := resP) (t := T) (fun v hv => (hS v).1 hv), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hpT => ?_
  have hfib : S.filter (fun v => resP v = p) = (finite_mulSupport_adicAbv_natCast (F := F) (hT p hpT)).toFinset := by
    ext v
    rw [Finset.mem_filter, mem_finite_residueChar_eq (hT p hpT), hS]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hpT, h⟩
  rw [hfib]
  have hc : ∀ v ∈ (finite_mulSupport_adicAbv_natCast (F := F) (hT p hpT)).toFinset,
      (-Real.log (HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) * g (resP v) =
        (-Real.log (HeightOneSpectrum.adicAbv F v (p : F)) / Real.log p) * g p := by
    intro v hv
    rw [(mem_finite_residueChar_eq (hT p hpT) v).1 hv]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul, sum_localDeg_eq (hT p hpT), mul_comm]

end GlobalTheory.PlaceSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataOfFiniteIndexSubgroupStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagDomainData_of_finiteIndex_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 → ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  first | exact @GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero | exact GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero | (intros; apply GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolumeStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevelGroup_data_same_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, ∃ Y : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y.Ψ = (U.X k).Ψ ∧ Y.p0 = (U.X k).p0 ∧ Y.Gm = (U.X k).Gm ∧ Y.Λ = (U.X k).Λ ∧ Y.ξ0 = (U.X k).ξ0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y ∧ GlobalTheory.EqCovol.IsSelfDualTr Y ∧ GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol Y := by
  first | exact @GlobalTheory.EqCovol.exists_levGrp_covol | exact GlobalTheory.EqCovol.exists_levGrp_covol | (intros; apply GlobalTheory.EqCovol.exists_levGrp_covol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralWeylBasisSpanningAllRingsStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_weylBasis_spanning_all_rings : ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∃ (P : Type) (_ : Fintype P) (b : P → MvPolynomial (Fin n × Fin n) ℤ), LinearIndependent ℤ b ∧ (∀ (R : Type) [CommRing R], weyl R n n le_rfl ν = Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (b i))) ∧ ∀ (K : Type) [Field K] [CharZero K], dualWeyl K n n ν = Submodule.span K (Set.range fun i => MvPolynomial.map (Int.castRingHom K) (b i)) := by
  first | exact @GlobalTheory.WeylBasis.exists_weyl_basis | exact GlobalTheory.WeylBasis.exists_weyl_basis | (intros; apply GlobalTheory.WeylBasis.exists_weyl_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSelfDualTraceFormStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_indefinite_selfDualTraceForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (r : ℕ) (Y : Data E r), 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsSelfDualTr Y → ∃ z : Fin r → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  first | exact @GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr | exact GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr | (intros; apply GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelBlock
section
namespace GlobalTheory.GammaLevel

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_one_of_block (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (m : Frame X.Ψ r) (hm : ∀ τ (a c : Fin r), (c : ℕ) < X.p0 → X.p0 ≤ (a : ℕ) → m τ a c = 0)
    (h : lact γ x = rmul x m) : γ = 1 := by
  have hp0 := X.p0_le
  have hj : r - X.p0 ≤ r := Nat.sub_le _ _
  have hp : r - (r - X.p0) = X.p0 := by omega
  have hx' : lact γ x ∈ X.dom := FrameFibre.lact_mem_GG (X.Γ_stab γ hγ).1 hx
  have key : ∀ τ : X.Ψ, ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧
      (∀ a c : Fin r, (c : ℕ) < r - (r - X.p0) → ¬ (a : ℕ) < r - (r - X.p0) → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ mat m τ * b = b * t := by
    intro τ
    refine FreeOnDomain.exists_conj_block hj _ ?_
    ext a c
    refine hm τ _ _ ?_ ?_
    · rw [idx_symm_inr]; have := c.2; omega
    · rw [idx_symm_inl]; omega
  choose b t hb hb0 ht e using key
  have e' : ∀ τ, mat (lact γ x) τ * b τ = mat x τ * b τ * t τ := fun τ => by
    rw [Matrix.mul_assoc, ← e, h, ← Matrix.mul_assoc]
    rfl
  refine X.Γ_free γ hγ (rmul x fun τ => b τ)
    (GlobalTheory.PointOfFrames.rmul_mem_dom X hx _ hb (by rw [hp] at hb0; exact hb0)) (fun τ => t τ)
    (fun τ => ⟨?_, ht τ⟩) ?_
  · intro h0
    have h1 := congrArg det (e' τ)
    have h0' : (t τ).det = 0 := h0
    rw [det_mul, det_mul, h0', mul_zero] at h1
    exact mul_ne_zero (hx' τ).1 (hb τ) h1
  · exact (ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lact_rmul' X γ x _).trans (funext e')

omit [NumberField E] [IsCMField E] in

theorem lact_inv_mul {Ψ : Finset (E →+* ℂ)} {δ γ : GL (Fin r) E} {x m : Frame Ψ r}
    (h : lact γ x = rmul (lact δ x) m) : lact (δ⁻¹ * γ) x = rmul x m := by
  funext τ
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat m τ := congrFun h τ
  change ((δ⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ * mat m τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_level_block {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (h1 : 1 ≤ r) (k : U.Comp) (x x' : (U.X k).dom)
    (hxx : (U.un k x').x = (U.un k x).x) :
    ∃ (δ : GL (Fin r) E) (m : Frame (U.X k).Ψ r), IsUStab (U.X k).Gm (U.X k).Λ δ ∧
      (∀ u ∈ (U.X k).Λ, ∃ u' ∈ (U.X k).Λ, (δ : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u') ∧
      x'.1 = rmul (lact δ x.1) m ∧
      ∀ τ (a c : Fin r), (c : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (a : ℕ) → m τ a c = 0 := by
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨hκ, -, -, hrk, hinj, hspan, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU h1 W k
  obtain ⟨hr, hX, -⟩ := hU
  obtain ⟨hp0, hty⟩ := hX k
  obtain ⟨idx, hi, hper⟩ := CompInj.exists_idx hσ hr W.e (U.X k) hp0 hty
  have hq : (W.F.Di (W.ik k)).q = Dw.q := (W.F.sig _).2
  have hξ : cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hpos : ∀ τ ∈ (U.X k).Ψ, 0 < (τ (-(U.X k).ξ0)).im := by
    intro τ hτ
    have := (U.X k).κ0_sign ⟨τ, hτ⟩
    rw [hκ, map_mul, map_ofNat] at this
    rw [map_neg, Complex.neg_im]
    simp at this
    linarith
  let Pf : Frame (U.X k).Ψ r → ((W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)) := fun y =>
    AddMonoidHom.mk' (fun v j => Formalism.L2.PjFree.perFr (U.X k) y (W.emb k v)
      (Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2) (by
      intro a b
      funext j
      have he : ∀ τ : E →+* ℂ, Data.emb τ (W.emb k (a + b)) = Data.emb τ (W.emb k a) + Data.emb τ (W.emb k b) := by
        intro τ
        funext i
        simp [Data.emb]
      simp only [Pi.add_apply, hper, he]
      split_ifs
      · simp [hermC, mul_add, Finset.sum_add_distrib]
      · simp [Matrix.mulVec_add])
  have hpt : ∀ y : (U.X k).dom, (U.un k y).x = W.F.u (W.ik k) (Pf y.1) := by
    intro y
    obtain ⟨P, hP, -, hu, -⟩ := W.pt k y
    rw [hu]
    congr 1
    ext a j
    exact hP a j
  have hrange : LinearMap.range (W.emb k) = (U.X k).Λ := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (W.φ k a).2
    · intro hv
      exact ⟨(W.φ k).symm ⟨v, hv⟩, by simp [UW.emb]⟩
  obtain ⟨δ, m, hδ, hM, -, hm, hm0⟩ := FrameFibre.exists_level_block_of_eq E H Dw l Xo _ W.g _ W.F (W.ik k) r
    (-(U.X k).ξ0) (U.X k).Gm (W.emb k) (U.X k).Ψ idx Pf hty (by rw [hq]; exact hi) hξ hpos
    ⟨hinj, hspan, (U.X k).Gm_herm, (U.X k).Gm_det, W.isom k⟩ hrk
    (by rw [hq]; exact fun y v j => hper y _ j) x.1 (by rw [hq, ← hp0]; exact x.2) x'.1
    (by rw [hq, ← hp0]; exact x'.2) (by rw [← hpt, ← hpt, hxx])
  rw [hrange] at hδ
  rw [hq, ← hp0] at hm0
  refine ⟨δ, m, hδ, fun u hu => ?_, hm, hm0⟩
  obtain ⟨a, rfl⟩ : u ∈ LinearMap.range (W.emb k) := hrange ▸ hu
  obtain ⟨w, hw⟩ := hM a
  exact ⟨_, (W.φ k w).2, hw⟩

end

end GlobalTheory.GammaLevel

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.GammaLevel.trivial_mod_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp), (∀ δ : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ δ → (∀ u ∈ (U.X k).Λ, ∃ u' ∈ (U.X k).Λ, (δ : Matrix (Fin r) (Fin r) E).mulVec u = u + (l.M : ℕ) • u') → δ ∈ (U.X k).Γ) → ∀ γ ∈ (U.X k).Γ, (∀ u ∈ (U.X k).Λ, ∃ u' ∈ (U.X k).Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec u = u + (l.M : ℕ) • u') := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h1 _ k hP γ hγ
  obtain ⟨x, hx⟩ := GlobalTheory.CompInj.dom_nonempty (U.X k)
  have hx' : lact γ x ∈ (U.X k).dom := GlobalTheory.FrameFibre.lact_mem_GG ((U.X k).Γ_stab γ hγ).1 hx
  obtain ⟨t, ht⟩ := (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨_, hx'⟩).2 ⟨γ, hγ, fun _ => (1 : Matrix (Fin r) (Fin r) ℂ),
    fun τ => ⟨by
      change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
      simp, fun a c h => Matrix.one_apply_ne h.ne'⟩, by
      congr 1
      funext τ
      exact (Matrix.mul_one (mat (lact γ x) τ)).symm⟩
  obtain ⟨δ, m, hδ, hM, hm, hm0⟩ := GlobalTheory.GammaLevel.exists_level_block (U := Formalism.L2.PjFree.Unf.ofPj U) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) h1 k ⟨x, hx⟩ ⟨_, hx'⟩ ht.1
  have h := GlobalTheory.GammaLevel.eq_one_of_block (U.X k) (mul_mem (inv_mem (hP δ hδ hM)) hγ) hx m hm0
    (GlobalTheory.GammaLevel.lact_inv_mul hm)
  rw [inv_mul_eq_one] at h
  exact h ▸ hM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftDualWeylTensorReductionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_dualWeylTensorReduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange → ∀ P ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (mu τ)), ∃ y : NablaT O N mu, redT O N mu ϖ y = P := by
  first | exact @GlobalTheory.HighWtEmb.nabK_lift | exact GlobalTheory.HighWtEmb.nabK_lift | (intros; apply GlobalTheory.HighWtEmb.nabK_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrbitFamilyAdaptedLatticeSplitSupportStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (U : Subgroup G) (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), IsOrbitFamily (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (badN D) (wtA (κ i)) (T.dδ ((i : ℕ) + 1) (κ i).n) (fun u : U => ℓ u) (fun u => ((f u).1 : T.R ((i : ℕ) + 1))) → ∃ (a : 𝓞 T.Q.c.F) (s : ℕ) (f' : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ (∀ u, (s : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (a : T.Q.c.F) • ((f' u).1 : T.R ((i : ℕ) + 1))) ∧ SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧ (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧ Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ AdmX (l := T.Q.l) true x₀ ∧ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) ∧ ∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f' u).1 : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.OrbitAdapt.exists_adapted | exact GlobalTheory.OrbitAdapt.exists_adapted | (intros; apply GlobalTheory.OrbitAdapt.exists_adapted <;> assumption)
end

