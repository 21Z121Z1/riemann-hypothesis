import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0564
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0557
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuaProductEqGaussianDatumSmallModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

open GlobalTheory.SmallDat

theorem heisS_box_gen {t : T} {i j : ℕ} {e : Num G i j} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    {ψ : AddChar (AF D.host.F) ℂ} {f₁ : HomA G t i j → ℂ} {f₂ : HomB G i j → ℂ}
    (h₁ : IsLatVac (heisO ψ _ _) (latA G t i j) f₁) (h₂ : IsLatVac (heisO ψ _ _) (latB G i j) f₂) {v : Pl D.host.F}
    {γ : PtS G i j} (hγ : γ ∈ genPtS t e v) : heisS Γ ψ γ (boxS t e f₁ f₂) = boxS t e f₁ f₂ := by
  unfold IsLatVac at h₁ h₂
  rw [heisS_box t e Γ hW₁ hWW ψ γ f₁ f₂]
  rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγl, ε, hε, hxA, hxB⟩
  · have hdA : mapA t e (2 • γ') = 2 • mapA t e γ' := by rw [two_nsmul, two_nsmul, mapA_add]
    have hdB : mapB e (2 • γ') = 2 • mapB e γ' := by rw [two_nsmul, two_nsmul, mapB_add]
    rw [hdA, hdB, h₁.1 _ hγ'.2.1, h₂.1 _ hγ'.2.2]
  · rw [h₁.2 ε hε _ hγl.2.1 hxA, h₂.2 ε hε _ hγl.2.2 hxB]

variable {W : G.Weil} {t : T} {i j : Fin D.R.m} {M : Vol G} {e : Num G i j} {Bs : Base D.host.F D.host.E}
  {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : Chars D.host.F D.host.E} {om : Rep D.sp.cm.sig Γ.V Γ.W} {om' : Rep D.sp.cm.sig Γ.V' Γ.W}

theorem exists_vacS (hL : L.Is μ₀) (h : IsTripleOf W M t i j e Bs Γ X) (hT : IsTriple Bs Γ X om om')
    (hti : GlobalTheory.FlipMatch.IsDoublyCompatible t i j e Bs Γ X) {f₁ : HomA G t i j → ℂ} {f₂ : HomB G i j → ℂ}
    (h₁ : W.IsVac (.mu t i j) f₁) (h₂ : W.IsVac (.chi i j) f₂) :
    ∃ f, thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) = boxS t e f₁ f₂ := by
  have hψ : Bs.ψ = W.ψ := h.ψ
  have hGood : Γ.M'.IsGood W.ψ := hψ ▸ hT.geo.hM'
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := hψ ▸ hT.base.std
  obtain ⟨-, hvac₁⟩ := h₁
  obtain ⟨-, hvac₂⟩ := h₂
  have hbox := GlobalTheory.SmallDat.ThBox.thetaS_box W M t i j e Bs Γ X om om' h hT
  obtain ⟨Φ, hΦ, hΦθ⟩ := hbox.2.2 f₁ f₂ hvac₁.theta hvac₂.theta
  have hfix : ∀ v, ∀ γ ∈ genPtS t e v, Γ.M'.co.rho W.ψ γ Φ = Φ := by
    intro v γ hγ
    refine hbox.2.1 _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd γ Φ hΦ) _ hΦ ?_
    rw [thetaS_rho, hΦθ, heisS_box_gen h.JW₁ h.JWW hvac₁.lat hvac₂.lat hγ]
  have hsd := GlobalTheory.SmallDatLat.latPtS_le_closure_and_selfDual hL W t i j e Γ h.JW₁ h.JWW
  have hlat := GlobalTheory.SmallDat.latPtS_le_latAtV t i j e Bs Γ X hti
  obtain ⟨f, hf⟩ := GlobalTheory.PureGlue.eq_pure_of_slices Γ.M'.vac (fun v => (hGood.vac v).2.1) hGood.std Φ hΦ (by
    intro v y hy
    rcases isEmpty_or_nonempty (IxS G i j) with hκ | ⟨⟨k₀⟩⟩
    · refine ⟨(fun ξ : IxS G i j → _ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k))) default / Γ.M'.vac v default, fun ξ => ?_⟩
      have hξ : ξ = default := Subsingleton.elim _ _
      subst hξ
      have hv0 : Γ.M'.vac v default ≠ 0 := by
        intro h0
        apply (hGood.vac v).2.1
        funext ξ'
        rw [Subsingleton.elim ξ' default]
        exact h0
      rw [div_mul_cancel₀ _ hv0]
    obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded Γ.V' Γ.W v Γ.M'.co hT.geo.hV'.lat hT.geo.hW.lat
    have hsdl := GlobalTheory.LatVac.DualLoc.map_selfDual v Γ.M'.co W.ψ (latPtS t e v) (fun γ hγ => hγ.1) ((hsd v).2)
    have hcont : Continuous (GlobalTheory.LatVac.psiAt W.ψ v) := by
      show Continuous (fun x => W.ψ (GlobalTheory.LatVac.liftV v x))
      exact hstd.1.comp (continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v))
    have hne1 : GlobalTheory.LatVac.psiAt W.ψ v ≠ 1 := by
      intro h1
      obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer (K := D.host.F) v
      have hx : ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F) ∉ v.adicCompletionIntegers D.host.F := by
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ]
        first
        | decide
        | simp
        | (intro hle; have := (inv_le_one₀ (by simp)).1 hle; simp at this)
      have hall := (hsdl ((fun _ => c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)), 0)).2
        (fun l _ => by rw [h1, AddChar.one_apply])
      obtain ⟨γ, hγ, hγe⟩ := AddSubgroup.mem_map.1 hall
      have h2 := (hcb γ (hlat v γ hγ) k₀).1
      rw [hγe] at h2
      have h3 : c * (c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)) ∈ v.adicCompletionIntegers D.host.F := h2
      rw [mul_inv_cancel_left₀ hc0] at h3
      exact hx h3
    obtain ⟨a, ha⟩ := GlobalTheory.SchrFixUniq.proportional_of_fixed v (GlobalTheory.LatVac.psiAt W.ψ v) hcont hne1
      (GlobalTheory.LatVac.locCo Γ.M'.co v '' genPtS t e v) ((latPtS t e v).map (GlobalTheory.LatVac.locCo Γ.M'.co v)) c
      ((AddSubgroup.map_mono ((hsd v).1)).trans (AddMonoidHom.map_closure _ _).le) hc0 hsdl
      (by
        intro l hl k
        obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.1 hl
        exact hcb γ (hlat v γ hγ) k)
      (Γ.M'.vac v) (fun ξ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact GlobalTheory.BigDat.schr_eq_of_acts Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hGood.vac v).1
          (GlobalTheory.SmallDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT v (hlat v) γ hγ))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact GlobalTheory.BigDat.schr_slice Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hfix v γ hγ) hy)
      (hGood.vac v).2.1
    exact ⟨a, fun ξ => by simpa using congrFun ha ξ⟩)
  exact ⟨f, by rw [← hf, hΦθ]⟩

end GlobalTheory.SmallVac

namespace GlobalTheory.SmallVac

open GlobalTheory.SmallDat GlobalTheory.FlipMatch

theorem vac_datumB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M'.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumB (t := t) W e Γ (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) := by
  intro D T L sc G μ₀ hL W ρ t i j M hst e Bs Γ X om om' h hT hti
  have h₁ : W.IsVac (.mu t i j) (ρ.vT i j) := ρ.vT_is t i j i.2.le j.2
  have h₂ : W.IsVac (.chi i j) (ρ.vX i j) := ρ.vX_is i j i.2 j.2.le
  obtain ⟨f, hf⟩ := exists_vacS hL h hT hti h₁ h₂
  have hGood : Γ.M'.IsGood Bs.ψ := hT.geo.hM'
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    obtain ⟨x₁, hx₁⟩ : ∃ x : HomA G t i j, ρ.vT i j x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact GlobalTheory.BigDat.vac_ne_zero h₁ (funext hc)
    obtain ⟨x₂, hx₂⟩ : ∃ x : HomB G i j, ρ.vX i j x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact GlobalTheory.BigDat.vac_ne_zero h₂ (funext hc)
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf _ _) Γ.M'.vac =
        (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf _ _) Γ.M'.vac := by
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    have hu := congrFun hf (ofMaps t e (x₁, x₂))
    rw [h0, thetaS_smul, zero_mul] at hu
    unfold boxS at hu
    rw [mapA_ofMaps, mapB_ofMaps] at hu
    exact mul_ne_zero hx₁ hx₂ hu.symm
  · exact GlobalTheory.SmallGauss.isGauss W M t i j e Bs Γ X om om' h hT _ _ h₁ h₂ 1 f (by rw [one_smul]; exact hf)
  · exact GlobalTheory.TensUniq.pure_mem_schA f _ (fun v => (hGood.vac v).1) hGood.std
  · intro u
    erw [Finsupp.sum_single_index, one_mul]
    · exact congrFun hf u
    · exact zero_mul _

end GlobalTheory.SmallVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInBasisIntegralAtConjugatePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

variable {D : D7}

theorem entries_of_mem_GLint {L : Type} [Field L] {n : ℕ} (O : Subring L) {g : GL (Fin n) L}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) (i j : Fin n) : g.1 i j ∈ O ∧ (g⁻¹).1 i j ∈ O := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨(h.1 i j).2, by rw [← map_inv]; exact ((h⁻¹).1 i j).2⟩

theorem frame_change {n : ℕ} {β β' : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (i j : Fin n) : (β⁻¹ * β').1 i j ∈ OA D := by
  have h1 : β'.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := (h' _).2 fun k => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 := (h _).1 h1 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
  exact h2

theorem dual_frame {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsFrame β Λ) (hd : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ) :
    ∃ β' : GL (Fin V.rank) (Lev.EAf D), Formalism.UG.cT (cjA D) β.val * V.gram.map (inc D) * β'.val = 1 ∧
      (∀ i j, (β⁻¹ * β').1 i j ∈ OA D) ∧ (∀ i j, (β'⁻¹ * β).1 i j ∈ OA D) := by
  have hL := GlobalTheory.DiagLiftFix.isLattice_of_isFrame hβ
  have hΛ := GlobalTheory.StdFrames.eq_lat hβ hL
  obtain ⟨β', h1, -⟩ := exists_dual_frame V β
  have e : GlobalTheory.NormSum.AdLattice.lat β' = Λ := by rw [← dualL_lat_eq h1, ← hΛ, hd]
  have h' : IsFrame β' Λ := e ▸ GlobalTheory.StdFrames.isFrame_lat β'
  exact ⟨β', h1, frame_change hβ h', frame_change h' hβ⟩

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

theorem conj_formula_gen {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ}
    (J B Bi B' B'i Z Zi : Matrix (Fin n) (Fin n) A) (hB : B * Bi = 1) (hB' : B' * B'i = 1) (hZ : Z * Zi = 1)
    (h1 : Formalism.UG.cT σ B * J * B' = 1) (hz : Formalism.UG.cT σ Z * J * Z = J) :
    Bi * Z * B = Bi * B' * Formalism.UG.cT σ (Bi * Zi * B) * (B'i * B) := by
  have hcBi : Formalism.UG.cT σ Bi * Formalism.UG.cT σ B = 1 := by
    rw [← GlobalTheory.StdFrames.cT_mul', hB, GlobalTheory.StdFrames.cT_one']
  have hzi : Formalism.UG.cT σ Zi * Formalism.UG.cT σ Z = 1 := by
    rw [← GlobalTheory.StdFrames.cT_mul', hZ, GlobalTheory.StdFrames.cT_one']
  have hM : Formalism.UG.cT σ B * J = B'i := by
    calc Formalism.UG.cT σ B * J = Formalism.UG.cT σ B * J * (B' * B'i) := by rw [hB', Matrix.mul_one]
      _ = B'i := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h1' : B' * (Formalism.UG.cT σ B * J) = 1 := by rw [hM, hB']
  have hz' : Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Z * J * Z) = J * Z := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hzi, Matrix.one_mul]
  rw [GlobalTheory.StdFrames.cT_mul', GlobalTheory.StdFrames.cT_mul', ← hM]
  calc Bi * Z * B = Bi * (B' * (Formalism.UG.cT σ B * J)) * Z * B := by rw [h1', Matrix.mul_one]
    _ = Bi * B' * Formalism.UG.cT σ B * (Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Z * J * Z)) * B := by
        rw [hz']
        simp only [Matrix.mul_assoc]
    _ = Bi * B' * Formalism.UG.cT σ B * (Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Bi * Formalism.UG.cT σ B) * J) * B := by
        rw [hz, hcBi, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

variable {D : D7}

theorem conj_formula {n : ℕ} (J : Matrix (Fin n) (Fin n) (Lev.EAf D)) (β β' z : GL (Fin n) (Lev.EAf D))
    (h1 : Formalism.UG.cT (cjA D) β.val * J * β'.val = 1) (hz : Formalism.UG.cT (cjA D) z.val * J * z.val = J) :
    (β⁻¹ * z * β).val = (β⁻¹ * β').val * Formalism.UG.cT (cjA D) (β⁻¹ * z⁻¹ * β).val * (β'⁻¹ * β).val := by
  simp only [Units.val_mul]
  exact conj_formula_gen (cjA D) J β.val (β⁻¹).val β'.val (β'⁻¹).val z.val (z⁻¹).val
    (Units.mul_inv β) (Units.mul_inv β') (Units.mul_inv z) h1 hz

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

variable {D : D7}

theorem cpt_conj_mem {n : ℕ} (w : Pl D.host.E) (P C M : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (hP : ∀ i j, P i j ∈ OA D) (hM : ∀ i j, M i j ∈ OA D)
    (hC : ∀ i j, cpt w (C i j) ∈ w.adicCompletionIntegers D.host.E) (i j : Fin n) :
    cpt (Formalism.DivisionValues.conjPl w) ((P * Formalism.UG.cT (cjA D) C * M) i j) ∈
      (Formalism.DivisionValues.conjPl w).adicCompletionIntegers D.host.E := by
  rw [GlobalTheory.FunObj.conjPl_eq_cP]
  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine sum_mem fun l _ => mul_mem (sum_mem fun k _ => mul_mem ?_ ?_) ?_
  · exact (mem_OA_iff _).1 (hP i k) _
  · exact ConjugatePlaceIntegrality.GlobalTheory.CompanionTheory.ConjPlaceInt.cpt_sg_mem_integers w (C l k) (hC l k)
  · exact (mem_OA_iff _).1 (hM l j) _

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

theorem inBasis_conjPl_mem_KO : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsFrame β Λ → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∀ x ∈ UA D.sp.cm V.gram, ∀ w : Pl D.host.E, inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin V.rank) → inBasis rfl β (Formalism.DivisionValues.conjPl w) x ∈ GlobalTheory.SplitWeil.KO (Kw (Formalism.DivisionValues.conjPl w)) (Fin V.rank) := by
  intro D V β Λ hβ hd x hx w hw
  obtain ⟨β', h1, hP, hM⟩ := dual_frame hβ hd
  have hu : ∀ z ∈ UA D.sp.cm V.gram, Formalism.UG.cT (cjA D) z.val * V.gram.map (inc D) * z.val = V.gram.map (inc D) :=
    fun z hz => hz
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion] at hw ⊢
  have hC : ∀ a b, cpt w ((β⁻¹ * x * β).val a b) ∈ w.adicCompletionIntegers D.host.E := fun a b =>
    (entries_of_mem_GLint _ hw a b).1
  have hC' : ∀ a b, cpt w ((β⁻¹ * x⁻¹ * β).val a b) ∈ w.adicCompletionIntegers D.host.E := fun a b => by
    have := (entries_of_mem_GLint _ hw a b).2
    rw [← map_inv] at this
    exact this
  refine GlobalTheory.FunObj.mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [GlobalTheory.FunObj.inBasis_apply, conj_formula _ β β' x h1 (hu x hx)]
    exact cpt_conj_mem w _ _ _ hP hM hC' _ _
  · rw [← map_inv, GlobalTheory.FunObj.inBasis_apply]
    have e := conj_formula _ β β' x⁻¹ h1 (hu _ (inv_mem hx))
    rw [inv_inv] at e
    rw [e]
    exact cpt_conj_mem w _ _ _ hP hM hC _ _

end GlobalTheory.ConjPlaceUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacMoveHigh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove in
theorem vac_move_high : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      ∃ c : ℂ, W.om (.top t (j + 1)) (((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        c • Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  intro D T L sc G W U S t ht Φ β j hj k hk e he Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hce : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hce
  have hW := W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hvac := S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hS := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m by omega))
  have hT := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
  set g : GA D (G.V (.top (j + 1))) := ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
    FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))) with hgdef
  have key := GlobalTheory.SplitLinear.splitLinearModel D W.ψ _ _ _ _ _ hW _ _ hS hT (locPl G t) e he _ hvac.2.theta hvac.2.lat 1
    one_ne_zero Tm hTm (cutPart (e + cA D e) _ g) 1 (suppAt_cutPart hee hce _ g) (GlobalTheory.SplitLinear.suppAt_one e _) _ _
    (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) _ (GlobalTheory.isSBHalf_halfInd e _)
  have hinf : infPart D (e + cA D e) = 0 := by
    rw [RingHom.map_add, ho.infPart_eq, infPart_cA ho.infPart_eq, add_zero]
  have hgfin : g ∈ GfC (G.V (.top (j + 1))) := ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2
  have hg1fin : cutPart (e + cA D e) _ g ∈ GfC (G.V (.top (j + 1))) :=
    GlobalTheory.IdemSupport.mem_GfC_of_suppF _ hinf (suppAt_cutPart hee hce _ g)
  have hg2fin : cutPart (1 - (e + cA D e)) _ g ∈ GfC (G.V (.top (j + 1))) := by
    have e1 : cutPart (1 - (e + cA D e)) _ g = (cutPart (e + cA D e) _ g)⁻¹ * g := by
      rw [eq_inv_mul_iff_mul_eq, ← cutPart_mul hf]
    rw [e1]
    exact mul_mem (inv_mem hg1fin) hgfin
  have hΛ : ∀ u, u ∈ stdLatO S (.top t (j + 1)) ↔
      ∃ u₀ ∈ stdLatO S (.top t (j + 1)), u = actO _ _ (cutPart (1 - (e + cA D e)) _ g) 1 u₀ :=
    GlobalTheory.T.offPlacesPart_movedLevel_keeps_standardHomLattice S ht j hj k hk e he
  have hV := G.isV (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) fun _ h => by cases h
  have hV' := G.isV (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega) fun _ h => by cases h
  have hv' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ hW W.θ_is _ _ _ _ _ _ _ _ (cutPart (1 - (e + cA D e)) _ g) 1
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hg2fin τ, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ (one_mem _) τ, Matrix.mul_one, Matrix.one_mul]) hΛ _ hvac
  obtain ⟨c₂, -, hc₂⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ hV.sigOK hV'.sigOK
    (W.cart_is _ (show j + 1 ≤ D.R.m by omega)) (W.cart_is _ (show j + 1 + 1 ≤ D.R.m by omega)) _ _ hS hT _ _ hvac hv'
  have hvacTm : Tm (halfInd e (stdLatO S (.top t (j + 1)))) = S.Z.vac (.top t (j + 1)) := by
    have := hTm.vac
    rwa [one_smul] at this
  refine ⟨c₂ * ((splitFacO (G.chrS (.top t (j + 1) : Pair T)) (G.chrT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ)), ?_⟩
  calc W.om (.top t (j + 1)) (g, 1) (S.Z.vac (.top t (j + 1)))
      = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1)
          (W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) _ g, 1) (S.Z.vac (.top t (j + 1)))) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← cutPart_mul hf]
    _ = c₂ • W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1) (S.Z.vac (.top t (j + 1))) := by
        rw [hc₂, map_smul]
    _ = _ := by
        rw [← hvacTm]
        erw [key]
        conv_rhs => rw [mul_smul, ← map_smul]
        congr 2
        funext x
        rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitLinear.subst_eq, halfInd_cutPart hee hce]
        rfl

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorSumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_split_place_indicator_sum : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  first | exact @GlobalTheory.SplitDetModule.modu_norm_det_split | exact GlobalTheory.SplitDetModule.modu_norm_det_split | (intros; apply GlobalTheory.SplitDetModule.modu_norm_det_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDetStageVariablesEmbedGLEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical

noncomputable section
namespace GlobalTheory.StepLeft

def splitVar {n m σ : Type} (P : (n ⊕ m) × σ → Prop) (Q : σ → Prop) (h : ∀ r s, P (Sum.inl r, s) ↔ Q s) :
    (n × {s // Q s}) ⊕ {ls : m × σ // P (Sum.inr ls.1, ls.2)} ≃ {rs // P rs} where
  toFun := Sum.elim (fun a => ⟨(Sum.inl a.1, a.2.1), (h _ _).2 a.2.2⟩) (fun a => ⟨(Sum.inr a.1.1, a.1.2), a.2⟩)
  invFun := fun a => match a with
    | ⟨(Sum.inl r, s), hs⟩ => Sum.inl (r, ⟨s, (h _ _).1 hs⟩)
    | ⟨(Sum.inr l, s), hs⟩ => Sum.inr ⟨(l, s), hs⟩
  left_inv := by rintro (⟨r, s, hs⟩ | ⟨⟨l, s⟩, hs⟩) <;> rfl
  right_inv := by rintro ⟨⟨r | r, s⟩, hs⟩ <;> rfl

theorem det_colwise_fromBlocks {k : Type} [CommRing k] {n m σ : Type} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] [Fintype σ] (P : (n ⊕ m) × σ → Prop) (Q : σ → Prop) (h : ∀ r s, P (Sum.inl r, s) ↔ Q s)
    [Fintype {rs // P rs}] [DecidableEq {rs // P rs}] (κ : Matrix n n k)
    (M : Matrix {rs // P rs} {rs // P rs} k)
    (hM : ∀ a b, M a b = if a.1.2 = b.1.2 then (fromBlocks κ 0 0 1 : Matrix (n ⊕ m) (n ⊕ m) k) a.1.1 b.1.1 else 0) :
    M.det = κ.det ^ Fintype.card {s // Q s} := by
  rw [← det_submatrix_equiv_self (splitVar P Q h) M]
  have : M.submatrix (splitVar P Q h) (splitVar P Q h) =
      fromBlocks (blockDiagonal fun _ : {s // Q s} => κ) 0 0 1 := by
    ext a b
    rcases a with (⟨r, s, hs⟩ | ⟨⟨l, s⟩, hs⟩) <;> rcases b with (⟨r', s', hs'⟩ | ⟨⟨l', s'⟩, hs'⟩) <;>
      simp [hM, splitVar, blockDiagonal_apply, one_apply]
    by_cases h1 : s = s' <;> by_cases h2 : l = l' <;> simp [h1, h2]
  rw [this, det_fromBlocks_zero₂₁, det_blockDiagonal]
  simp

theorem valuation_det_stepLin_embX : ∀ {k : Type} [Field k] [ValuativeRel k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (κ : GL n k), valuation k (gdet κ : k) = 1 → valuation k (stepLin n' (embX c κ).val).det = 1 := by
  intro k _ _ n n' _ _ _ _ c κ hκ
  let Q : n' ⊕ Fin (c + 1) → Prop := Sum.elim (fun _ => False)
    (fun i => c / 2 + 1 < i.val + 1 ∨ (Even c ∧ i.val = c / 2))
  have h : ∀ (r : n) s, (Free (c := c) (c / 2 + 1) (Sum.inl r, s) ∨ Kept (c := c) (Sum.inl r, s)) ↔ Q s := by
    rintro r (s | s) <;> simp [Q, Free, Kept]
  rw [det_colwise_fromBlocks (fun rs => Free (c / 2 + 1) rs ∨ Kept rs) Q h κ.val _ (fun a b => by
    simp only [stepLin, of_apply]; split_ifs <;> rfl), map_pow]
  have : valuation k κ.val.det = 1 := hκ
  rw [this, one_pow]

end GlobalTheory.StepLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeCoordsRationalPointMulEqCoordMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertexLatticeCoords_rationalPoint_mul_eq_coordMatrix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (r : FinPt G X) (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E),
    GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U → ∀ x : FinPt G X,
      GlobalTheory.SumSize.latAt S X (r * x) = SDLat.smulLat U.1 (GlobalTheory.SumSize.latAt S X x) := by
  first | exact @GlobalTheory.RatMoveLat.latAt_rat | exact GlobalTheory.RatMoveLat.latAt_rat | (intros; apply GlobalTheory.RatMoveLat.latAt_rat <;> assumption)
end

