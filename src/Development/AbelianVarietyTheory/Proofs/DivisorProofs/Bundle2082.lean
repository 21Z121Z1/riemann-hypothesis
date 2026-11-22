import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.SemistableReduction.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightShiftEqDetMul
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProof
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped Matrix

noncomputable section

namespace GlobalTheory.SmallElement

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem span_L' {r : ℕ} (X : DataX E r) :
    Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro x hx
  have h1 := X.NA_sub x hx
  have hNA : (X.NA : E) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
  have e : x = (X.NA : E)⁻¹ • ((X.NA : E) • x) := by rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem trace_sub_mem {r : ℕ} (X : DataX E r) (g : ℕ) (hg : IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g)
    (δ : GL (Fin r) E) (hδ : IsUStab X.Gm X.L' δ)
    (hu : IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g δ) :
    ∃ z : 𝓞 E, (δ : Matrix (Fin r) (Fin r) E).trace - r = (g : E) * z := by
  classical
  set N : Matrix (Fin r) (Fin r) E := (δ : Matrix (Fin r) (Fin r) E) - 1 with hNdef
  have htr : N.trace = (δ : Matrix (Fin r) (Fin r) E).trace - r := by
    simp [hNdef, Matrix.trace_sub]
  have hN : ∀ x ∈ X.L', N.mulVec x ∈ X.L' := fun x hx => by
    rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact X.L'.sub_mem ((hδ.2 x).1 hx) hx
  have hP : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), ∃ z ∈ P, ((z : 𝓞 E) : E) = N.trace :=
    fun P hP => by
      obtain ⟨k, hk⟩ := hu P hP
      exact GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul E r X.L' N P k X.L'_fg (span_L' X) hP.1 hN hk
  have hne : ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hg.2]
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne'
  obtain ⟨P0, hP0⟩ := hne
  obtain ⟨t, -, ht⟩ := hP P0 hP0
  have hall : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), t ∈ P := fun P hP' => by
    obtain ⟨z, hz, hzt⟩ := hP P hP'
    have : z = t := RingOfIntegers.ext (hzt.trans ht.symm)
    exact this ▸ hz
  have hpZ : Prime (g : ℤ) := Nat.prime_iff_prime_int.1 hg.1
  haveI hpr : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
    hpr.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hrad := GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver E g hg.1 hg.2
  have hmem : t ∈ Ideal.span {(g : 𝓞 E)} := by
    apply hrad
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J hJ => ?_
    obtain ⟨hJle, hJp⟩ := hJ
    apply hall J
    refine ⟨hJp, ⟨?_⟩⟩
    have hle : Ideal.span {(g : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) J := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) (g : ℤ) ∈ J
      rw [map_natCast]
      exact hJle (Ideal.mem_span_singleton_self _)
    exact hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) hle
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨z, ?_⟩
  rw [← htr, ← ht, ← hz]
  push_cast
  ring

end GlobalTheory.SmallElement

namespace GlobalTheory.SmallElement

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem map_conj_mulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (M.map (starRingEnd ℂ)) *ᵥ u = star (M *ᵥ star u) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem normSq_star {r : ℕ} (u : Fin r → ℂ) : ReciprocityTheory.MultiplicativeHeights.normSq (star u) = ReciprocityTheory.MultiplicativeHeights.normSq u := by
  simp [ReciprocityTheory.MultiplicativeHeights.normSq]

theorem exp_sq (r : ℕ) : Real.exp (1 / (3 * (r : ℝ))) ^ 2 = Real.exp (2 / (3 * (r : ℝ))) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem det_ne_of_mul_eq_one {r : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ} (h : A * B = 1) : A.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem map_conj_mul_eq_one {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ} (hA : IsUnit A.det) :
    (A⁻¹).map (starRingEnd ℂ) * A.map (starRingEnd ℂ) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.SmallElement

namespace GlobalTheory.SmallElement

theorem smallElement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E := by
  intro E _ _ _ r X g hg hgr Γo hstab hunip x hx hNC γ hγ hs
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Units.ext (Matrix.ext fun i => i.elim0)
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X.toData x hx
  have hx1 := ModeHalfA.dom_of_orth X.toData h1
  have hu : ∀ τ : X.Ψ, IsUnit (mat x1 τ).det :=
    fun τ => isUnit_iff_ne_zero.2 (LUPf.orthogonalFrame_det_ne_zero X.toData x1 h1 τ)
  have hmaj : ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj (rmul x1 b) τ v = ReciprocityTheory.MultiplicativeHeights.normSq ((mat x1 τ)⁻¹ *ᵥ v) := fun τ v => by
    rw [GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, ModeHalfA.maj_orth X.toData h1]
    rfl
  have hcΨ : ∀ σ : E →+* ℂ, σ ∉ X.Ψ → ComplexEmbedding.conjugate σ ∈ X.Ψ := fun σ hσ =>
    not_not.1 fun h' => hσ ((X.cmType σ).2 h')
  let Q : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ := fun σ =>
    if hσ : σ ∈ X.Ψ then (mat x1 ⟨σ, hσ⟩)⁻¹
    else ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ)
  have hQpos : ∀ σ (hσ : σ ∈ X.Ψ), Q σ = (mat x1 ⟨σ, hσ⟩)⁻¹ := fun σ hσ => dif_pos hσ
  have hQneg : ∀ σ (hσ : σ ∉ X.Ψ),
      Q σ = ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ) :=
    fun σ hσ => dif_neg hσ
  set G : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hG
  have hposB : ∀ (τ : X.Ψ) (u : Fin r → ℂ),
      ReciprocityTheory.MultiplicativeHeights.normSq (((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹) *ᵥ u) ≤
        Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u := by
    intro τ u
    have h := hs τ (mat x1 τ *ᵥ u)
    have e : (mat x1 τ)⁻¹ *ᵥ (mat x1 τ *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu τ), Matrix.one_mulVec]
    rw [hmaj, hmaj, e, exp_sq] at h
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h
  have hQdet : ∀ σ, (Q σ).det ≠ 0 := by
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · rw [hQpos σ hσ]
      exact det_ne_of_mul_eq_one (Matrix.nonsing_inv_mul _ (hu _))
    · rw [hQneg σ hσ]
      exact det_ne_of_mul_eq_one (map_conj_mul_eq_one (hu _))
  have hop : ∀ σ (u : Fin r → ℂ), ReciprocityTheory.MultiplicativeHeights.normSq ((Q σ * G.map σ * (Q σ)⁻¹) *ᵥ u) ≤
      Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u := by
    intro σ u
    by_cases hσ : σ ∈ X.Ψ
    · rw [hQpos σ hσ]
      exact hposB ⟨σ, hσ⟩ u
    · rw [hQneg σ hσ]
      set τ : X.Ψ := ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩ with hτ
      have hinv : (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ = (mat x1 τ).map (starRingEnd ℂ) :=
        Matrix.inv_eq_right_inv (map_conj_mul_eq_one (hu τ))
      have hGm : G.map σ = (G.map τ.1).map (starRingEnd ℂ) := by
        ext i j
        simp [hτ, ComplexEmbedding.conjugate_coe_eq]
      have e : ((mat x1 τ)⁻¹).map (starRingEnd ℂ) * G.map σ *
          (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ =
          ((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹).map (starRingEnd ℂ) := by
        rw [hinv, hGm, Matrix.nonsing_inv_nonsing_inv _ (hu τ), Matrix.map_mul, Matrix.map_mul]
      rw [e, map_conj_mulVec, normSq_star, ← normSq_star u]
      exact hposB τ (star u)
  have htr : ∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 E, (G ^ n).trace - r = (g : E) * z := by
    intro n _ _
    have hm := Γo.pow_mem hγ n
    have := trace_sub_mem X g hg (γ ^ n) (hstab _ hm) (hunip _ hm)
    rwa [Units.val_pow_eq_pow_val] at this
  have hg' : (Real.exp (1 / 3) + 1) * r < g := by
    have h3 := ReciprocityTheory.MultiplicativeHeights.sb_exp_third_lt_two
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hg3 : (3 * r : ℝ) < g := by exact_mod_cast hgr
    nlinarith
  have hU := ReciprocityTheory.MultiplicativeHeights.unipotent_holds E r g G Q htr hg' hQdet hop
  have hN : G - 1 = 0 := by
    refine hNC (G - 1) (fun v hv => ?_) (fun τ => ?_)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact X.L'.sub_mem (((hstab γ hγ).2 v).1 hv) hv
    · set S := ∑ a, ∑ b, ‖(Q τ.1 * (G.map τ.1 - 1) * (Q τ.1)⁻¹) a b‖ ^ 2 with hS
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hS1 : S < 1 := hU.2 τ.1
      refine ⟨Real.sqrt S, Real.sqrt_nonneg _, (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hS1),
        fun u => ?_⟩
      rw [Real.sq_sqrt hS0, hmaj, hmaj]
      have hmap : (G - 1).map τ.1 = G.map τ.1 - 1 := by
        rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply]
      have hQτ : Q τ.1 = (mat x1 τ)⁻¹ := hQpos τ.1 τ.2
      have e2 : (mat x1 τ)⁻¹ *ᵥ ((G.map τ.1 - 1) *ᵥ u) =
          ((mat x1 τ)⁻¹ * (G.map τ.1 - 1) * ((mat x1 τ)⁻¹)⁻¹) *ᵥ ((mat x1 τ)⁻¹ *ᵥ u) := by
        rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ)]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ),
          Matrix.mul_one]
      rw [hmap, e2, hS, hQτ]
      exact ReciprocityTheory.MultiplicativeHeights.sb_normSq_mulVec_le _ _
  exact Units.ext (sub_eq_zero.1 hN)

end GlobalTheory.SmallElement
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibilityStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_rows_bar_phase_compatibility : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.Rows → BarTie (fw2 p) ∧ (∀ i, OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i) ∧ ∀ i, PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  first | exact @GlobalTheory.BigOn.ompins_onto | exact GlobalTheory.BigOn.ompins_onto | (intros; apply GlobalTheory.BigOn.ompins_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsUniformLinksRankStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_rows_uniform_links_rank : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.Rows → (R2 p).LUnif ∧ BaseLinks (R2 p) (F2 p) ∧ RankRows (S2 p) := by
  first | exact @GlobalTheory.BigOn.SplitRows.unif_baseLinks_rankRows | exact GlobalTheory.BigOn.SplitRows.unif_baseLinks_rankRows | (intros; apply GlobalTheory.BigOn.SplitRows.unif_baseLinks_rankRows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareFlipReachesLocalQuotientClassesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareFlip_reaches_localQuotient_classes : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v, w.under (𝓞 D.host.F) = v → ∀ φ₀ ∈ GlobalTheory.WeilM.SB _,
    ∃ n Φ φ₂ g φ₃, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧ IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) φ₂ ∧
      φ₃ ∈ GlobalTheory.WeilM.SB _ ∧ Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ₂ φ₃ ∧ Rf.p v φ₃ = Rf.p v φ₀ := by
  first | exact @GlobalTheory.SquareFlipReach.flip_reach | exact GlobalTheory.SquareFlipReach.flip_reach | (intros; apply GlobalTheory.SquareFlipReach.flip_reach <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepCharacterUniformiserValueUnitAwayTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.TwistStepVal

theorem isAwayUnit_loc {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] (σ : K →+* ℂ)
    (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ} (hinf : χ.HasInf φ n)
    {w : HeightOneSpectrum (𝓞 L)} (hw : χ.UnrAt w) (y : (w.adicCompletion L)ˣ) (hy : Formalism.L2.Host.IsUnifAt w y)
    {m : ℕ} (hm : Ideal.absNorm w.asIdeal ∣ m) {x : K} (hx : σ x = ((χ.loc w y : ℂˣ) : ℂ)) :
    GlobalTheory.Square.IsAwayUnit m x := by
  have hq : 0 < Ideal.absNorm w.asIdeal :=
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine GlobalTheory.Square.isAwayUnit_of_unitOff_embedding σ x _ m hq hm ?_
  rw [hx, Formalism.L2.Host.HChar.val_eq χ hw y hy]
  exact GlobalTheory.ValUnitLevel.unitOff_val L χ I φ n w _ hinf hw (Ideal.absNorm_mem _)

theorem step_val : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ twPl G t →
      ∃ x : D.what₂.LL, D.what₂.embLL x = ((chrW (GlobalTheory.SqStep.chs G i j t).ν τ (unifAt v) : ℂˣ) : ℂ) ∧
        GlobalTheory.Square.IsAwayUnit (Qn G t) x := by
  intro D T Lc sc G W S μ₀ hL hN i j t v τ hμ hχ htw
  rw [GlobalTheory.SqStepArith.chrW_chs G hL]
  have hy : Formalism.L2.Host.IsUnifAt (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom (unifAt v)) := by
    show Valued.v (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ) ((unifAt v : (Fv D.host.F v)ˣ) : Fv D.host.F v))
      = WithZero.exp (-1 : ℤ)
    rw [GlobalTheory.LFun.SplitTie.valued_complMap τ (GlobalTheory.AdelicU.splitPrime_under τ), GlobalTheory.ChrWUnif.valued_unifAt]
  generalize Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom (unifAt v) = y at hy ⊢
  have hm : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have e : ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) =
      ((Lc.C.mu0 j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) * ((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) *
        ((G.ch.chiH (D.R.m - i)).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ)⁻¹ := by
    simp [nuH, Formalism.L2.Host.HChar.loc, div_eq_mul_inv]
  obtain ⟨a, ha⟩ := hN.chars.mu0 j (GlobalTheory.AdelicU.splitPrime τ) y
  obtain ⟨b, hb⟩ := hN.chars.xi t (GlobalTheory.AdelicU.splitPrime τ) y
  obtain ⟨c, hc⟩ := hN.chars.chi (D.R.m - i) hm (Nat.sub_le _ _) (GlobalTheory.AdelicU.splitPrime τ) y
  have hQ : 0 < Qn G t := Finset.prod_pos fun w _ =>
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdvd : Ideal.absNorm (GlobalTheory.AdelicU.splitPrime τ).asIdeal ∣ Qn G t :=
    Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 D.host.E) => Ideal.absNorm w.asIdeal) htw
  refine ⟨a * b * c⁻¹, by rw [e, map_mul, map_mul, map_inv₀, ha, hb, hc], ?_⟩
  obtain ⟨n, -, hn⟩ := (Lc.C.isMu0 j).inf
  have ua := isAwayUnit_loc D.what₂.embLL _ hn hμ y hy hdvd ha
  have uc := isAwayUnit_loc D.what₂.embLL _ (G.ch.inf _ hm (Nat.sub_le _ _)) hχ y hy hdvd hc
  obtain ⟨k, hk, hξ⟩ := hL.xi_fin t
  have ub : GlobalTheory.Square.IsAwayUnit (Qn G t) b := by
    refine GlobalTheory.Square.AwayClosure.of_pow_eq_one _ hk (D.what₂.embLL.injective ?_)
    rw [map_pow, hb, map_one, ← Units.val_pow_eq_pow_val]
    have h1 : (Lc.xiH t ^ k).loc (GlobalTheory.AdelicU.splitPrime τ) y = 1 := by
      rw [show Lc.xiH t ^ k = 1 from hξ]; rfl
    rw [← Units.val_one, ← h1]
    simp [Formalism.L2.Host.HChar.loc]
  exact GlobalTheory.Square.AwayClosure.mul (GlobalTheory.Square.AwayClosure.mul ua ub) (GlobalTheory.Square.AwayClosure.inv hQ uc)

end GlobalTheory.TwistStepVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExpansionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SumExpAt

theorem mem_locP {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

theorem locIncl_of_equiv {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (e : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (N D : Submodule (𝓞 K) V) (N' D' : Submodule (𝓞 K) V')
    (hN : N.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = N')
    (hD : D.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = D')
    (h : ∀ x ∈ N', a • x ∈ Formalism.HermitianLatticesTheory.localization₂ p D') : ∀ v ∈ N, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p D := by
  intro v hv
  set f : V →ₗ[𝓞 K] V' := (e : V →ₗ[K] V').restrictScalars (𝓞 K) with hf
  have hx : f v ∈ N' := hN ▸ Submodule.mem_map_of_mem hv
  obtain ⟨s, hs, hsD⟩ := (mem_locP p D' _).1 (h _ hx)
  refine (mem_locP p D _).2 ⟨s, hs, ?_⟩
  rw [← hD] at hsD
  obtain ⟨y, hy, hye⟩ := hsD
  have hinj : Function.Injective f := e.injective
  have : y = s • a • v := hinj (by rw [hye, map_smul, map_smul])
  rw [← this]
  exact hy

theorem cutLat_locIncl {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.DIV.CSD K) {d : ℕ}
    (E : Matrix (Fin S.dim) (Fin d) K) (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (h : ∀ c, ∀ v ∈ S.Nab c, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p (S.Del c)) :
    ∀ z ∈ Formalism.DivisionValues.cutLat E S.nabLat, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ p (Formalism.DivisionValues.cutLat E S.delLat) := by
  classical
  intro z hz
  have hz' : ∀ c, S.I (E.mulVec z) c ∈ S.Nab c := fun c => hz c (Set.mem_univ c)
  have hlin : ∀ (r : 𝓞 K) (y : Fin d → K), S.I (E.mulVec (r • y)) = r • S.I (E.mulVec y) := fun r y => by
    have h1 := ((Matrix.mulVecLin E).restrictScalars (𝓞 K)).map_smul r y
    have h2 := (S.I.restrictScalars (𝓞 K)).map_smul r (E.mulVec y)
    simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at h1 h2
    rw [h1, h2]
  choose s hs hsD using fun c => (mem_locP p (S.Del c) _).1 (h c _ (hz' c))
  refine (mem_locP p _ _).2 ⟨∏ c, s c, prod_mem fun c _ => hs c, ?_⟩
  intro c _
  show S.I (E.mulVec ((∏ c, s c) • a • z)) c ∈ S.Del c
  rw [hlin, hlin, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ c), Pi.smul_apply, Pi.smul_apply, mul_comm,
    mul_smul]
  exact Submodule.smul_mem _ _ (hsD c)

end GlobalTheory.SumExpAt

namespace GlobalTheory.SumExpAt

open Formalism.CohomologicalDescent.LD in

theorem exZ_res_eq_natW (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) (f : ℕ → ℕ) (c : ℤ)
    (hc : ∀ a : Fin n, (f a : ℤ) = lam.w a + c) (l : ℕ) (hl : l.Prime) :
    Formalism.CohomologicalDescent.LA.exZ n n le_rfl (res n f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl lam.natW l := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · congr 1
    funext a
    exact a.elim0
  · let m : Fin n := ⟨n - 1, by omega⟩
    have hds : lam.detShift = lam.w m := by
      simp only [Formalism.BasicNotions.DomWeight.detShift, dif_pos hn]
      rfl
    have hres : res n f = fun a => lam.natW a + f m := by
      funext a
      have h1 := hc a
      have h2 := hc m
      have h3 : lam.w m ≤ lam.w a := lam.anti (Fin.le_def.2 (by simp only [m]; omega))
      have h4 : ((lam.w a - lam.w m).toNat : ℤ) = lam.w a - lam.w m := Int.toNat_of_nonneg (by omega)
      change f a.val = (lam.w a - lam.detShift).toNat + f m
      rw [hds]
      omega
    have hanti : Antitone lam.natW := fun i j hij => by
      have := lam.anti hij
      exact Int.toNat_le_toNat (by omega)
    rw [hres]
    exact Formalism.CohomologicalDescent.LA.exact_z_twist_by_det n lam.natW (f m) l hanti hl

theorem exZ_res_congr {N n : ℕ} (h : N = n) (f : ℕ → ℕ) (l : ℕ) :
    Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Formalism.CohomologicalDescent.LD.res N f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl (Formalism.CohomologicalDescent.LD.res n f) l := by
  subst h
  rfl

end GlobalTheory.SumExpAt

namespace GlobalTheory.ExpTie

open GlobalTheory.SumExpAt
open Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem lIncl_sumExp (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (hD : Dict L j P W) (t : p.P.T)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := p.charW.base.fam.tie
  obtain ⟨e, -, -, -, hNab, hDel⟩ := hT.coefL j t
  have hJ : W.JA P (Formalism.EigenvalueLevelCeiling.plc w) = ∑ τ, Formalism.CohomologicalDescent.LA.exZ (Vc D j).rank (Vc D j).rank le_rfl
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ).natW (Formalism.EigenvalueLevelCeiling.plc w) := by
    unfold Wts.JA Wts.ex
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [exZ_res_congr hD.Nr]
    obtain ⟨c, hc⟩ := hD.lam τ
    exact exZ_res_eq_natW _ _ _ c hc _ (Formalism.EigenvalueLevelCeiling.plc_prime w)
  intro z hz
  rw [hJ]
  refine cutLat_locIncl (blk p j t).S _ w.asIdeal _ (fun c => ?_) z hz
  refine locIncl_of_equiv e w.asIdeal _ _ _ _ _ (hNab c) (hDel c) ?_
  exact GlobalTheory.T.sum_exactExponents_smul_mem_localizedCoeffLattice _ _ _ _ _ _ _ (GlobalTheory.RepsCompare.isLattice_hLat _ _) w

end Point

theorem sumExpSt : SumExpSt :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => EvPt.of_forall fun _ _ _ p _ _ j P W hD _ t w => lIncl_sumExp p j P W hD t w⟩⟩
end GlobalTheory.ExpTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariantStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_unitary_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (g : UA σ X.J) (h : UA σ W.J) (x u : Matrix (Fin n) (Fin d) (AE F E)),
    symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u := by
  first | exact @GlobalTheory.SympInv.symp_act | exact GlobalTheory.SympInv.symp_act | (intros; apply GlobalTheory.SympInv.symp_act <;> assumption)
end

