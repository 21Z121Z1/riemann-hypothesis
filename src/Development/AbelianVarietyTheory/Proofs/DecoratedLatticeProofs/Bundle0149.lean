import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0131
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocModU

theorem upAdd {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x x' : Matrix Y Y' k) :
    p.up FS FT (x + x') = p.up FS FT x + p.up FS FT x' := by
  unfold Place.up
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp [Matrix.map_apply]

theorem upZero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : p.up FS FT 0 = 0 := by
  unfold Place.up
  ext i j
  simp [Matrix.map_apply]

theorem charZero_of_place {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) : CharZero k :=
  (RingHom.charZero_iff (ϕ := p.π.comp (incA D)) (RingHom.injective _)).1 inferInstance

theorem localModel_uniq_transport_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₀, Φ₀ ≠ 0 → T₁ Φ₀ = T₂ Φ₀ → T₁ = T₂) ∧ (∀ T₁, p.IsModel ψ FS FT T₁ → ∀ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) → (∀ f, IsThetaFunO ψ S T f → ∀ y : WO S T, IsHalf (p.e + cA D p.e) y → A (heisO ψ S T y f) = heisO ψ S T y (A f)) → p.IsModel ψ FS FT (A ∘ₗ T₁)) ∧ ∀ f₀, IsThetaFunO ψ S T f₀ → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → heisO ψ S T (p.up FS FT x) f₀ = f₀) → (∀ y : WO S T, IsHalf (cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT x) y) = 1) → heisO ψ S T y f₀ = f₀) → ∃ T₁, p.IsModel ψ FS FT T₁ ∧ ∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → T₁ Φ = f₀ := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ
  haveI : CharZero k := charZero_of_place p
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨hup, -, -, hsymk, hsurj⟩ := GlobalTheory.T.heisenberg_frame_half_inverse D k p Y Y' S T FS FT ψ ψk hψk
  obtain ⟨-, hec, -⟩ := p.split
  have hce : cA D p.e * p.e = 0 := by rw [mul_comm, hec]
  have hcce : cA D (cA D p.e) * cA D p.e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, hec]
  have halfSum1 : ∀ u : WO S T, IsHalf p.e u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have halfSum2 : ∀ u : WO S T, IsHalf (cA D p.e) u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro T₁ T₂ h₁ h₂ Φ₀ hΦ₀ h12
    let W : Submodule ℂ (Matrix Y Y' k → ℂ) := (LinearMap.ker (T₁ - T₂)).map (SB (Matrix Y Y' k)).subtype
    have memW : ∀ Φ : SB (Matrix Y Y' k), Φ.1 ∈ W ↔ T₁ Φ = T₂ Φ := by
      intro Φ
      constructor
      · rintro ⟨Ψ, hΨ, hΨe⟩
        have : Ψ = Φ := Subtype.ext hΨe
        subst this
        simpa [sub_eq_zero] using hΨ
      · intro h
        exact ⟨Φ, by simpa [sub_eq_zero] using h, rfl⟩
    have hWle : W ≤ SB (Matrix Y Y' k) := by
      rintro _ ⟨Ψ, -, rfl⟩
      exact Ψ.2
    have hWeq := GlobalTheory.T.schwartzBruhat_matrix_translation_modulation_irreducible k Y Y' ψk hcont hne W hWle
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ x hx
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        refine (memW ⟨_, hx⟩).2 ?_
        rw [h₁.trans x Φ ⟨_, hx⟩ (fun t => rfl), h₂.trans x Φ ⟨_, hx⟩ (fun t => rfl), hΦ'])
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ b hb
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have hmod : ∀ t, (⟨_, hb⟩ : SB (Matrix Y Y' k)).1 t = ψ (symplO S T (p.up FS FT t) y) * Φ.1 t := by
          intro t
          show _ = _
          rw [hsymk t y hy, hyb t]
          rfl
        refine (memW ⟨_, hb⟩).2 ?_
        rw [h₁.modul y hy Φ _ hmod, h₂.modul y hy Φ _ hmod, hΦ'])
      Φ₀.1 ((memW Φ₀).2 h12) (fun h => hΦ₀ (Subtype.ext h))
    ext1 Φ
    have hm : Φ.1 ∈ W := by rw [hWeq]; exact Φ.2
    exact (memW Φ).1 hm
  ·
    intro T₁ h₁ A hA1 hA2
    refine ⟨fun Φ => hA1 _ (h₁.theta Φ), fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
    · show A (T₁ Φ') = heisO ψ S T (p.up FS FT x) (A (T₁ Φ))
      rw [h₁.trans x Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum1 _ (hup x).1)]
    · show A (T₁ Φ') = heisO ψ S T y (A (T₁ Φ))
      rw [h₁.modul y hy Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum2 _ hy)]
  ·
    intro f₀ hf₀ hfx hfy
    let Z := GlobalTheory.PlaceModel.half S T (cA D p.e)
    let χ : Matrix Y Y' k → Z → ℂ := fun t z => ψ (symplO S T (p.up FS FT t) z.1)
    have hZ : ∀ z : Z, IsHalf (cA D p.e) z.1 := fun z => (GlobalTheory.PlaceModel.isHalf_iff S T).2 z.2
    obtain ⟨Tm, htr, hmo, hvac, hspan⟩ := GlobalTheory.T.exists_schrodinger_intertwiner_integralMatrices k Y Y' Z χ
      (fun a b z => by simp only [χ, upAdd, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul])
      (fun a z z' => by simp only [χ, AddSubgroup.coe_add, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul])
      (fun z => by simp only [χ, upZero, GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one])
      (fun a => by simp only [χ, ZeroMemClass.coe_zero, GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one])
      (fun n hn z => by
        obtain ⟨z', hz', e⟩ := GlobalTheory.PlaceModel.half_div S T (cA D p.e) n hn z.1 z.2
        exact ⟨⟨z', hz'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact e)⟩)
      (fun n hn z z' h => by
        apply Subtype.ext
        have h' : n • z.1 = n • z'.1 := by
          have := congrArg Subtype.val h
          simpa only [AddSubgroup.coe_nsmul] using this
        rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hn z.1, h', GlobalTheory.PlaceModel.inv_smul_nsmul S T hn])
      (fun x hx => GlobalTheory.T.matrix_integral_of_addChar_trace_dual k Y Y' ψk hcont hne x fun b hb => by
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have key : ∀ t, χ t ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ = ((ψk (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) := by
          intro t
          show ψ _ = _
          rw [hsymk t y hy, hyb t]
        have := hx ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ (fun u hu => by
          rw [key, hb u hu, Circle.coe_one])
        rw [key] at this
        exact Circle.ext (by simpa using this))
      (WO S T → ℂ) (fun x => GlobalTheory.PlaceModel.heisL S T ψ (p.up FS FT x)) (fun z => GlobalTheory.PlaceModel.heisL S T ψ z.1)
      (fun x x' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hce _ ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x).1) _
          ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x').1), upAdd])
      (fun z z' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hcce _ z.2 _ z'.2]
        rfl)
      (fun x z f => GlobalTheory.PlaceModel.heisL_comm S T ψ _ _ f)
      (fun f => by
        rw [upZero]
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      (fun f => by
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      f₀ (fun u hu => hfx u hu)
      (fun z hz => hfy z.1 (hZ z) hz)
    have hsplit := p.split
    have hstd : IsCharAF D.host.F ψ := hψ.1
    refine ⟨Tm, ⟨fun Φ => ?_, fun x Φ Φ' h => htr x Φ Φ' h, fun y hy Φ Φ' h =>
      hmo ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ Φ Φ' h⟩, hvac⟩
    have hs := hspan Φ
    generalize Tm Φ = g at hs
    induction hs using Submodule.span_induction with
    | mem _ hw =>
      obtain ⟨w, rfl⟩ := hw
      exact GlobalTheory.FinTranslate.isTheta_heisO_fin hstd (GlobalTheory.SplitScalar.half_fin hsplit (hup w.1).1)
        (GlobalTheory.FinTranslate.isTheta_heisO_fin hstd
          (GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj hsplit) (hZ w.2)) hf₀)
    | zero => exact GlobalTheory.WeilVacMove.isTheta_zero
    | add _ _ _ _ h1 h2 => exact GlobalTheory.WeilVacMove.isTheta_add h1 h2
    | smul c _ _ h1 => exact GlobalTheory.WeilVacMove.isTheta_smul c h1

end GlobalTheory.LocModU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormsMatrixStepsCoupledFactorBoundedAnyLevelPrim
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem factors_leS : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (B : Base D D.host.ccK dl) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok), FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), (∀ i, i + 2 < N.R.m → StepBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) i (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (i + 1))) ∧ CplBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (N.R.m - 1) + liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ N.R.m)  := by
  intro hB hT hV hL hR hP
  obtain ⟨Cd, hdat⟩ := GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size
  obtain ⟨C₁, hC₁, hker⟩ := GlobalTheory.T.chainKernel_bound_at_embedding_anyLevelPrime hB hT hV hL hR hP Cd
  obtain ⟨Cc, hCc, hcl⟩ := GlobalTheory.ChainClassNumbersS.classNumbers_leS
  obtain ⟨Ci, hCi, hidx⟩ := GlobalTheory.T.card_matrixStep_indices_le_exp
  obtain ⟨Cy, hCy, hyb⟩ := GlobalTheory.CouplingCosetsS.ncard_ybSet_le
  refine ⟨C₁ + (Cc + Ci + Cy), by positivity, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B b hY hK hF hE hFD M _ hM ρ
  have hPr : Pr.Ok := H.1.2.2.2.2.2.2.2.2.2.1
  have hU := errUnit_nonneg N (hPr.T_prime u).one_lt.le
  have hm := N.R.two_le_m
  set U := errUnit N (Pr.T u) with hUdef
  set σ : X.K →+* ℂ := (ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1) with hσ
  set Q := KerChain.ofCol W Ch sel mu cst I
    (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE with hQ
  set kb : ℕ → ℝ := fun j => kernelBound_sq N δ (Pr.T u) C₁ j (fun z => logOmAt B cD M ρ (s.iT (pl z)))
    (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1 with hkb
  have hlift : ∀ j, kb j + 2 * ((Cc + Ci + Cy) * U) ≤
      liftBound_sq N s W Ch sel mu cst I B cD pl u δ (C₁ + (Cc + Ci + Cy)) M ρ j := fun j =>
    kernelBound_ge N δ _ _ _ j _ _ _ _ _ _
  have hpos : ∀ {n : ℕ} (lam : X.Tau → DomWeight n),
      ((Matrix.of fun i j => pairVr X.emb lam 1 (bVV X.K lam i) (bVV X.K lam j)).map
        (placeUnder s.σ₀ hM.1 ρ).embedding).PosSemidef := fun lam => (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb _ lam _).1
  have hsq := fun {n : ℕ} (lam : X.Tau → DomWeight n) => (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb n lam σ).2
  have hk := hker CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B hFD
  obtain ⟨hc1, hc2, -⟩ := hcl CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hi1 := hidx CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hfam : ∀ j, ∀ φ : (Q.F j).Forms, 0 ≤ (famIpAt (Q.F j) (Q.hF j) (placeUnder s.σ₀ hM.1 ρ) φ φ).re := by
    intro j φ
    unfold famIpAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b' _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    refine mul_nonneg (by positivity) ?_
    exact (sqAt_nonneg (W.lamTrue u j) σ _).trans_eq (hsq (W.lamTrue u j) _).symm
  have hone : (1 : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (Cd * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
    have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
    exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le h0 h1)
  refine ⟨fun i hi φ => ?_, fun φ => ?_⟩
  · have h1 := GlobalTheory.T.sq_norm_classSumMatrix_le_cauchySchwarz X.K Q i (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (i + 1))) (Real.exp (Cc * U)) (Real.exp (Cc * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (fun _ => hpos (W.lamTrue u i))
      (fun _ => hpos (W.lamTrue u (i + 1))) (hc1 i (by omega)) (hc1 (i + 1) (by omega)) (by
        intro al be p p' x
        have h2 := hk i (i + 1) rfl (by omega) _ (frsF sel mu p) _ (frsF sel mu p') ⟨p.deco.2.lat, p.deco.2.uni⟩
          ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ (hdat CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p') M hM ρ x
        have e : (Q.kk i al be).k p p' = matK W Ch sel mu cst I (chTh W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2)) i al be p p' := by
          exact congrArg (fun k : ClsKer _ _ => k.k p p') (dif_pos (show i < N.R.m - 2 by omega))
        rw [e]
        exact (hsq (W.lamTrue u (i + 1)) _).trans_le (h2.trans_eq (congrArg _ (hsq (W.lamTrue u i) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam i φ))
    have b1 : (Fintype.card (Q.F i).β : ℝ) ≤ Real.exp (Ci * U) := hi1 i (by omega)
    have b2 : (Fintype.card (Q.F (i + 1)).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (i + 1) (by omega)
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) * Real.exp (kb (i + 1)) := by gcongr
      _ ≤ _ := by
        simp only [← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (hlift _))
        nlinarith [mul_nonneg hCy hU]
  · have hNle : N.R.N (N.R.m - 2 + 1) ≤ N.Nm := by
      unfold NumDatum.Nm Ranks.N
      have : N.R.m - 2 + 1 ≤ N.R.m := by omega
      gcongr
    have h1 := GlobalTheory.T.coupled_class_sum_cauchy_schwarz X.K Q (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (N.R.m - 2 + 1))) (Real.exp (kb N.R.m))
      (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cy * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le
      (fun _ => hpos (W.lamTrue u (N.R.m - 2))) (hpos (W.lamTrue u (N.R.m - 2 + 1))) (hpos (W.lamTrue u N.R.m))
      (hc1 (N.R.m - 2) (by omega)) (hc1 (N.R.m - 2 + 1) (by omega) b) hc2
      (fun p => (hyb CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H _ hNle).2 _ p.deco.2.lat) (by
        intro al p₀ p Y hYm x
        have h2 := hk (N.R.m - 2) (N.R.m - 2 + 1) rfl (by omega) _ (frsF sel mu p₀) _ (frsF sel mu p)
          ⟨p₀.deco.2.lat, p₀.deco.2.uni⟩ ⟨p.deco.2.lat, p.deco.2.uni⟩ _
          ((GlobalTheory.T.firstCoupledKernel_finiteDatum_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H al p₀ p Y).mono hone) M hM ρ x
        have e : (Q.cp al).k1 p₀ p Y = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2) (W.lamTrue u (N.R.m - 2 + 1)))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N (frsF sel mu p₀) p.deco.1.N (frsF sel mu p)
            (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2)) _).symm))) (by
        intro al p d Y hYm x
        have h2 := hk (N.R.m - 2 + 1) N.R.m (by omega) (by omega) _ (frsF sel mu p) _ (frsT sel mu u d)
          ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ _
          ((GlobalTheory.T.lastKernelFiniteDatum_bounded_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H p d Y hYm).mono hone) M hM ρ x
        have e : (Q.cp al).k2 p Y d = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2 + 1) (W.lamTrue u N.R.m))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p) (tilQ sel mu u d).1.N
            (frsT sel mu u d) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u N.R.m) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam _ φ))
    have b1 : (Fintype.card (Q.F Q.n).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (N.R.m - 2) (by omega)
    have e1 : N.R.m - 2 + 1 = N.R.m - 1 := by omega
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) ^ 2 * Real.exp (Cc * U) * Real.exp (Cy * U) ^ 2 *
          Real.exp (kb (N.R.m - 2 + 1)) * Real.exp (kb N.R.m) := by gcongr
      _ ≤ _ := by
        simp only [sq, ← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (add_le_add (hlift _) (hlift _)))
        rw [e1]
        nlinarith [mul_nonneg hCy hU, mul_nonneg hCi hU]

end GlobalTheory.Core.Ht2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuasiMeasurePreservingAdelicUnitriangularLeftMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.LeftUniQmp

theorem qmp_left_uni : ∀ (D : D7) (ρ n : ℕ) (μ : Measure (Mx D ρ n)), μ.IsAddHaarMeasure → ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (fun b : Mx D ρ n => u.1.1 ⬝ b) μ μ := by
  intro D ρ n μ hμ u
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ n
  haveI : BorelSpace (Mx D ρ n) := ⟨rfl⟩
  have hc : Continuous (fun b : Mx D ρ n => u.1.1 ⬝ b) := continuous_const.matrix_mul continuous_id
  have hc' : Continuous (fun b : Mx D ρ n => (u.1⁻¹).1 ⬝ b) := continuous_const.matrix_mul continuous_id
  let T : Mx D ρ n ≃+ Mx D ρ n :=
    { toFun := fun b => u.1.1 ⬝ b
      invFun := fun b => (u.1⁻¹).1 ⬝ b
      left_inv := fun b => by
        show (u.1⁻¹).1 ⬝ (u.1.1 ⬝ b) = b
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun b => by
        show u.1.1 ⬝ ((u.1⁻¹).1 ⬝ b) = b
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun a b => Matrix.mul_add _ _ _ }
  haveI : (μ.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ T hc hc'
  refine ⟨hc.measurable, ?_⟩
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map T) μ
  show μ.map T ≪ μ
  rw [e]
  exact Measure.smul_absolutelyContinuous

end GlobalTheory.LeftUniQmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuasiMeasurePreservingSkewHermitianCongruenceUni
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.SkewConjQmp

theorem skewConj_matMul {D : D7} {ρ : ℕ} (a b : Mx D ρ ρ) (c : skewA D ρ) :
    skewConj (a ⬝ b) c = skewConj a (skewConj b c) := by
  apply Subtype.ext
  simp only [skewConj, adj_mul, Matrix.mul_assoc]

theorem skewConj_matOne {D : D7} {ρ : ℕ} (c : skewA D ρ) : skewConj (1 : Mx D ρ ρ) c = c := by
  apply Subtype.ext
  simp only [skewConj, adj_one, Matrix.one_mul, Matrix.mul_one]

theorem skewConj_addArg {D : D7} {ρ : ℕ} (a : Mx D ρ ρ) (c d : skewA D ρ) :
    skewConj a (c + d) = skewConj a c + skewConj a d := by
  apply Subtype.ext
  simp only [skewConj, AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]

theorem continuous_skewConj_arg {D : D7} {ρ : ℕ} (a : Mx D ρ ρ) : Continuous (skewConj a : skewA D ρ → skewA D ρ) := by
  have h1 : Continuous fun c : skewA D ρ => (a ⬝ c.1 : Mx D ρ ρ) := continuous_const.matrix_mul continuous_subtype_val
  have h2 : Continuous fun c : skewA D ρ => (a ⬝ c.1 ⬝ adj a : Mx D ρ ρ) := h1.matrix_mul continuous_const
  exact Continuous.subtype_mk h2 _

noncomputable def skewConjEquiv {D : D7} {ρ : ℕ} (g : GL (Fin ρ) (AE D)) : skewA D ρ ≃+ skewA D ρ where
  toFun := skewConj g.val
  invFun := skewConj (g⁻¹).val
  left_inv c := by
    rw [← skewConj_matMul]
    have : (g⁻¹).val ⬝ g.val = 1 := Units.inv_mul g
    rw [this, skewConj_matOne]
  right_inv c := by
    rw [← skewConj_matMul]
    have : g.val ⬝ (g⁻¹).val = 1 := Units.mul_inv g
    rw [this, skewConj_matOne]
  map_add' := skewConj_addArg _

set_option synthInstance.maxHeartbeats 200000 in

theorem quasiMeasurePreserving_skewConj : ∀ (D : D7) (ρ : ℕ) (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure →
    ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (skewConj u.1.1) lC lC := by
  intro D ρ lC hC u
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D ρ ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  have hcl : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) := isClosed_eq continuous_adj continuous_neg
  have : LocallyCompactSpace (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  have : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hc := continuous_skewConj_arg (u.1.1 : Mx D ρ ρ)
  have hH : (lC.map (skewConj u.1.1)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lC (skewConjEquiv u.1) hc
      (continuous_skewConj_arg (u.1⁻¹).val)
  refine ⟨hc.measurable, ?_⟩
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _

end GlobalTheory.Unf.SkewConjQmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvectionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_linear_generated_by_transvections : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) → ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R), u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  first | exact @GlobalTheory.GLGen.mem_of_det_eq_one | exact GlobalTheory.GLGen.mem_of_det_eq_one | (intros; apply GlobalTheory.GLGen.mem_of_det_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearLawHalfVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_linearLaw_halfVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Lat S)
    (ΛT : Lat T) (e : AE D) (f₀ : WO S T → ℂ)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsSplitIdem D e → IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀) →
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ →
      om (g, h) (Tm Φ) = GlobalTheory.SplitLinear.fac S T χS χT x y • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  first | exact @GlobalTheory.SplitLinearHalf.law_half | exact GlobalTheory.SplitLinearHalf.law_half | (intros; apply GlobalTheory.SplitLinearHalf.law_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalCharacterIsUnramifiedOfHeckeUnramStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceLocalCharacter_isUnramified_of_heckeUnramified : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ p.v → IsUnram (GlobalTheory.SplitLinAt.lam p χ r) := by
  first | exact @GlobalTheory.SplitLinUnram.lam_unram | exact GlobalTheory.SplitLinUnram.lam_unram | (intros; apply GlobalTheory.SplitLinUnram.lam_unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmFieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableRangeOne_adeles_cmField : ∀ (D : D7) (a b : AE D), IsCoprime a b → ∃ t : AE D, IsUnit (a + t * b) := by
  first | exact @GlobalTheory.StableRange.adeles_stableRange_one | exact GlobalTheory.StableRange.adeles_stableRange_one | (intros; apply GlobalTheory.StableRange.adeles_stableRange_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (o.boxS T fA fB)) ∧ (∀ fA fB, o.boxS T fA fB 0 = fA 0 * fB 0) ∧ (∀ fA fB, (∀ u, heisO ψ S T ((o.resS T).symm (u, 0)) (o.boxS T fA fB) = o.boxS T (heisO ψ A T u fA) fB) ∧ ∀ v, heisO ψ S T ((o.resS T).symm (0, v)) (o.boxS T fA fB) = o.boxS T fA (heisO ψ B T v fB)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ v, IsThetaFunO ψ A T fun u => f ((o.resS T).symm (u, v))) ∧ ∀ u, IsThetaFunO ψ B T fun v => f ((o.resS T).symm (u, v)) := by
  first | exact @GlobalTheory.BoxSlice.main | exact GlobalTheory.BoxSlice.main | (intros; apply GlobalTheory.BoxSlice.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionalInvarianceProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_functional_invariance_product : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ e, IsSplitIdem D e → ∀ (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ) (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ), (∀ u : WO A T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ A T f → ℓA (heisO ψ A T u f) = ℓA f) → (∀ u : WO B T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ B T f → ℓB (heisO ψ B T u f) = ℓB f) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → ℓ (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  first | exact @GlobalTheory.ProdForm.exists_product_form | exact GlobalTheory.ProdForm.exists_product_form | (intros; apply GlobalTheory.ProdForm.exists_product_form <;> assumption)
end

