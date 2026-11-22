import Mathlib
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0257
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0259
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveInducedModuleShift
section
noncomputable section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem isKFin_map {n : ℕ} (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : H' →ₗᵢ[ℂ] H)
    (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w)) {v : H'} (hv : IsKFin ε ρ' v) :
    IsKFin ε ρ (T v) := by
  obtain ⟨S, hS, hvS, hK⟩ := hv
  refine ⟨S.map T.toLinearMap, inferInstance, ⟨v, hvS, rfl⟩, ?_⟩
  rintro g hg _ ⟨w, hw, rfl⟩
  have hu : gᴴ * Jm ε * g = Jm ε := by
    rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.1 hg.1, Matrix.one_mul]
  obtain ⟨y, rfl, -⟩ := GlobalTheory.RealIwasawa.exists_uMat g hu
  exact ⟨_, hK _ hg w hw, hT y w⟩

end GlobalTheory.RealInd.Stages

namespace GlobalTheory.RealInd.Stages

theorem exists_stage {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (h : 0 < I.a)
    (hTL : GlobalTheory.Published.Langlands.TemperedLevi) :
    ∃ (I' : IndModule ε) (h' : 0 < I'.a), I'.j ⟨0, h'⟩ = 1 ∧ (I'.s ⟨0, h'⟩).re = (I.s ⟨0, h⟩).re ∧
      ∃ T : I'.H →ₗᵢ[ℂ] I.H, ∀ (g : UJ ε) (w : I'.H), T (I'.ρ (uMat g) w) = I.ρ (uMat g) (T w) := by
  obtain ⟨b, W', β, p, hW', hp, hl, hβ, hpos⟩ := GlobalTheory.T.refine_isotropic_flag I.flag
  have h6 := GlobalTheory.T.refined_flag_half_sum_of_roots n I.j hβ hpos
  have hp0 : p 0 = 0 := Fin.ext (by rw [hpos]; simp)
  have hb : 0 < b := by
    have := (h6 ⟨0, h⟩).1
    have h1 := I.pos ⟨0, h⟩
    have h2 : #{l | β l = ⟨0, h⟩} ≤ b := (card_filter_le _ _).trans (by simp)
    omega
  have hβ0 : β ⟨0, hb⟩ = ⟨0, h⟩ := by
    refine (hβ _ _).2 ⟨?_, ?_⟩
    · rw [show (⟨0, h⟩ : Fin I.a).castSucc = 0 from rfl, hp0]; exact Fin.zero_le _
    · obtain ⟨l, hl0⟩ : (univ.filter (fun l => β l = ⟨0, h⟩)).Nonempty := by
        rw [← card_pos, (h6 ⟨0, h⟩).1]; exact I.pos _
      have := ((hβ l ⟨0, h⟩).1 (mem_filter.1 hl0).2).2
      rw [Fin.lt_iff_val_lt_val] at this ⊢
      simp only [Fin.coe_castSucc] at this ⊢
      omega
  obtain ⟨U, _, _, _, τ, y, hτ, hμ⟩ := hTL n ε I.toDatum b W' hW' (fun i => ⟨p i, hp i⟩) hl
  have hKM : IsCompact ((KG ε : Set (UJ ε)) ∩ (I.M : Set (UJ ε))) :=
    (isCompact_iff_compactSpace.2 (instCompactKG n ε)).inter_right (isClosed_leviOne I.flag I.pos)
  haveI : CompactSpace ↥(KG ε ⊓ I.M) := isCompact_iff_compactSpace.1 hKM
  let μ : Measure ↥(KG ε ⊓ I.M) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  obtain ⟨ι, hι⟩ := hμ μ inferInstance inferInstance
  set s' := stageS I.j β I.s y with hs'def
  obtain ⟨H', _, _, _, ρ', ι', hm'⟩ := exists_isIndModel (σ := τ) hW' (fun _ => le_rfl)
    (fun m hm => hτ.2.2.1.2.1 _ ⟨m, hm, rfl⟩) s'
  let D' : Datum ε :=
    { a := b
      j := fun _ => 1
      W := W'
      flag := hW'
      pos := fun _ => le_rfl
      V := U
      σ := τ
      temp := hτ
      s := s' }
  let I' : IndModule ε := { D' with H := H', ρ := ρ', ι := ι', model := hm' }
  have h9 := GlobalTheory.T.stage_parameter_pairing_shift n I.j β I.s y I.pos (fun i => (h6 i).1) (fun i => (h6 i).2)
  have hs : ∀ x t, IsSplit ε W' x t → t ∈ leviOne ε I.W →
      pairing (fun _ => 1) s' x = pairing (fun _ => 1) (fun l => Complex.I * y l) x :=
    fun x t ht hm => h9.2 x (GlobalTheory.T.split_torus_levi_sum_vanishes hW' hp hβ ht hm)
  have h1 : ∀ v, τ 1 v = v := fun v => by
    rw [hτ.2.2.1.1.1]; rfl
  have hmem : ∀ F ∈ I'.fns, ∀ g, restr I.M F g ∈ indFun I.M (fun _ => 1) W' τ (fun l => Complex.I * y l) := fun F hF g => GlobalTheory.T.induction_in_stages_restriction τ s' y hs hF g
  have hcont : ∀ F ∈ I'.fns, Continuous F := fun F hF => (mem_indFun_top.1 hF).1
  have hΦ : ∀ F ∈ I'.fns, stageFun I.M _ ι F ∈ I.fns := fun F hF => mem_indFun_top.2
    ⟨GlobalTheory.T.stage_function_continuous I.M _ ι μ hι.norm_sq (hcont F hF) (hmem F hF),
     GlobalTheory.T.induction_in_stages_intertwining τ I.σ I.s s' _ ι (fun m hm u hu => GlobalTheory.T.levi_conjugates_unipotent_refined I.flag hW' hp hl hβ m hm.1 u hu)
      (fun x t ht => ⟨GlobalTheory.T.split_torus_refined_flag I.flag hW' hp hl hβ ht, fun m hm => GlobalTheory.T.levi_commutes_split_torus I.flag ht m hm.1⟩) h1 h9.1 hι.transl hF
      (hmem F hF)⟩
  let Φ : I'.fns →ₗ[ℂ] I.fns :=
    { toFun := fun F => ⟨stageFun I.M _ ι F.1, hΦ F.1 F.2⟩
      map_add' := fun F G => Subtype.ext (funext fun g => by
        change stageFun I.M _ ι (F.1 + G.1) g = stageFun I.M _ ι F.1 g + stageFun I.M _ ι G.1 g
        rw [stageFun_of_mem ι (hmem _ (I'.fns.add_mem F.2 G.2) g), stageFun_of_mem ι (hmem _ F.2 g),
          stageFun_of_mem ι (hmem _ G.2 g), ← map_add]
        exact congrArg ι (Subtype.ext (funext fun m => by
          by_cases hm : m ∈ I.M <;> simp [restr, hm])))
      map_smul' := fun c F => Subtype.ext (funext fun g => by
        change stageFun I.M _ ι (c • F.1) g = c • stageFun I.M _ ι F.1 g
        rw [stageFun_of_mem ι (hmem _ (I'.fns.smul_mem c F.2) g), stageFun_of_mem ι (hmem _ F.2 g), ← map_smul]
        exact congrArg ι (Subtype.ext (funext fun m => by
          by_cases hm : m ∈ I.M <;> simp [restr, hm]))) }
  have hnorm : ∀ F : I'.fns, ‖I.ι (Φ F)‖ = ‖ι' F‖ := fun F =>
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by
      rw [I.model.norm_sq, hm'.norm_sq]
      exact GlobalTheory.T.stage_function_norm_integral I.M _ ι μ hι.norm_sq (hcont _ F.2) (hmem _ F.2))
  have hΦtr : ∀ (F : I'.fns) (g : UJ ε),
      (Φ ⟨fun g' => F.1 (g' * g), indFun_mul_right F.2 trivial⟩).1 = fun g' => (Φ F).1 (g' * g) := fun F g =>
    funext fun g' => by
      change stageFun I.M _ ι (fun g' => F.1 (g' * g)) g' = stageFun I.M _ ι F.1 (g' * g)
      have : restr I.M (fun g' => F.1 (g' * g)) g' = restr I.M F.1 (g' * g) := funext fun m => by
        simp only [restr, mul_assoc]
      unfold stageFun
      rw [this]
  have hbd : ∃ C, ∀ F, ‖(I.ι ∘ₗ Φ) F‖ ≤ C * ‖ι' F‖ := ⟨1, fun F => by rw [one_mul]; exact (hnorm F).le⟩
  let T₀ := (I.ι ∘ₗ Φ).extendOfNorm ι'
  have hT₀ : ∀ F, T₀ (ι' F) = I.ι (Φ F) := LinearMap.extendOfNorm_eq hm'.dense hbd
  have hiso : ∀ v, ‖T₀ v‖ = ‖v‖ := fun v =>
    hm'.dense.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun F => by rw [hT₀]; exact hnorm F
  refine ⟨I', hb, rfl, ?_, ⟨T₀.toLinearMap, hiso⟩, fun g w => ?_⟩
  · change (s' ⟨0, hb⟩).re = _
    simp [hs'def, stageS, hβ0]
  · change T₀ (ρ' (uMat g) w) = I.ρ (uMat g) (T₀ w)
    refine hm'.dense.induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun F => ?_
    rw [hm'.transl g trivial F ⟨_, indFun_mul_right F.2 trivial⟩ (fun _ => rfl), hT₀, hT₀]
    exact (I.model.transl g trivial (Φ F) _ (fun g' => congrFun (hΦtr F g) g')).symm

end GlobalTheory.RealInd.Stages

namespace GlobalTheory.RealInd.Stages

theorem exists_first_step_one : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a) (χ : Fin n → ℂ), (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ (I' : IndModule ε) (h' : 0 < I'.a), I'.j ⟨0, h'⟩ = 1 ∧ (I'.s ⟨0, h'⟩).re = (I.s ⟨0, h⟩).re ∧ (∀ (k : ℕ) v, IsKFin ε I'.ρ v → ∃ N : ℕ, actU ε I'.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  intro hLC n ε I h χ hI
  obtain ⟨I', h', hj, hre, T, hT⟩ := exists_stage I h hLC.2.2.2.2.2.2
  refine ⟨I', h', hj, hre, fun k v hv => ?_⟩
  obtain ⟨N, hN⟩ := hI k (T v) (isKFin_map ε _ _ T hT hv)
  exact ⟨N, T.injective (by rw [← GlobalTheory.T.isometry_intertwines_enveloping ε _ _ T hT, hN, map_zero])⟩

end GlobalTheory.RealInd.Stages

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjXPreservesEmbeddingLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory

theorem projX_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e * d.qX) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d hA Λ 𝔟 v hv
  obtain ⟨hc, he, s, he'⟩ := hA
  obtain ⟨y, hy, u, hu, rfl⟩ := hv
  have hGh : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  set N : Matrix (Fin c) (Fin c) D.host.E := antiDiagonalSignGramMatrix c (-1) with hN
  have hK : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    simpa [Matrix.conjTranspose_mul, hGh, Matrix.mul_assoc] using this
  have hρc : ρ ≤ c := by omega
  let P : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = (Fin.castLE hρc p).rev then s p else 0
  let Q : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = Fin.castLE hρc p then (-D.host.xi0) ^ (p.1 + 1) else 0
  have heP : d.e' = a.a * P := by
    rw [he']; ext i p; rw [Matrix.mul_apply]; simp [colsOf, P, mul_comm]
  have heQ : d.e = a.a * Q := by
    rw [he]; ext i p; rw [Matrix.mul_apply]; simp [colsOf, Q, mul_comm]
  have hPN : ∀ p q, (Pᴴ * N) p q = if q = Fin.castLE hρc p then star (s p) else 0 := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    simp only [P, apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := p.2; have := q.2
    simp only [hN, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
    split_ifs <;> first | (exfalso; omega) | ring
  have hdiag : ∀ p : Fin ρ, star (s p) * (-D.host.xi0) ^ (p.1 + 1) = 1 := by
    intro p
    have h1 := d.e'e
    rw [heP, heQ, Matrix.conjTranspose_mul] at h1
    have h2 : Pᴴ * a.aᴴ * B.gram * (a.a * Q) = Pᴴ * N * Q := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [h2] at h1
    have h3 := congrFun (congrFun h1 p) p
    rw [Matrix.mul_apply] at h3
    simp only [hPN, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Q, Matrix.one_apply_eq] at h3
    simpa using h3
  have hqX : d.qX = Pᴴ * a.aᴴ * B.gram := by
    rw [HypDec.qX, heP, Matrix.conjTranspose_mul]
  have ht : d.qX *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = (Pᴴ * N) *ᵥ u := by
    have h1 : Pᴴ * a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
      calc _ = Pᴴ * (a.aᴴ * B.gram * frameMat B A a.ι) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hK, Matrix.mul_zero]
    have h2 : Pᴴ * a.aᴴ * B.gram * a.a = Pᴴ * N := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hqX, h1, h2, zero_mulVec, zero_add]
  have hu' : ∀ q : Fin c, (Q *ᵥ ((Pᴴ * N) *ᵥ u)) q = if q.1 < ρ then u q else 0 := by
    intro q
    simp only [mulVec, dotProduct, hPN, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Q]
    split_ifs with hq
    · rw [Finset.sum_eq_single ⟨q.1, hq⟩]
      · have e1 : q = Fin.castLE hρc ⟨q.1, hq⟩ := Fin.ext rfl
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [← mul_assoc, mul_comm ((-D.host.xi0) ^ _), hdiag, one_mul, if_pos e1, ← e1]
      · intro b _ hb
        rw [if_neg]
        intro e; apply hb; ext; simp only [Fin.ext_iff, Fin.val_castLE, Fin.val_mk] at e ⊢; omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro e; apply hq; rw [e]; simp
  refine ⟨0, Λ.zero_mem, Q *ᵥ ((Pᴴ * N) *ᵥ u), fun q => ?_, ?_⟩
  · rw [hu']; split_ifs
    · exact hu q
    · exact (𝔟 q).val.zero_mem
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, ht, heQ, ← mulVec_mulVec]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjYPreservesEmbeddingLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

variable {D : D7}

theorem colsOf_eq_mul {n c k : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (s : Fin k → D.host.E) :
    colsOf a f s = a * Matrix.of (fun q p => if q = f p then s p else 0) := by
  ext i p
  simp only [colsOf, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

theorem antiDiagonalGram_neg_one_castLE_row {c ρ : ℕ} (h : 2 * ρ ≤ c) (p : Fin ρ) (r : Fin c) :
    antiDiagonalSignGramMatrix c (-1 : D.host.E) (Fin.castLE (by omega) p) r = if r = (Fin.castLE (by omega) p : Fin c).rev then 1 else 0 := by
  have := p.2; have := r.2
  unfold antiDiagonalSignGramMatrix
  simp only [Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
  split_ifs <;> first | rfl | omega

theorem projY_mem_lat : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e' * d.qY) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d ⟨h, he, s, he'⟩ Λ 𝔟 v ⟨y, hy, u, hu, hv⟩
  subst hv
  set f : Fin ρ → Fin c := Fin.castLE (by omega) with hf
  set t : Fin ρ → D.host.E := fun p => (-D.host.xi0) ^ (p.1 + 1) with ht
  set Pe : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = f p then t p else 0) with hPe
  set Pe' : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = (f p).rev then s p else 0) with hPe'
  have hE : d.e = a.a * Pe := by rw [he, colsOf_eq_mul]
  have hE' : d.e' = a.a * Pe' := by rw [he', colsOf_eq_mul]
  have hG : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  have hperp' : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero, ← Matrix.mul_assoc] at this
  have hQF : d.qY * frameMat B A a.ι = 0 := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hperp', Matrix.mul_zero]
  have hQA : d.qY * a.a = Matrix.of (fun p r => if r = (f p).rev then star (t p) else 0) := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hgram]
    ext p r
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hPe, Matrix.of_apply, apply_ite star, star_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hf, antiDiagonalGram_neg_one_castLE_row h, mul_ite, mul_one, mul_zero]
  have hS : ∀ p, s p * star (t p) = 1 := by
    intro p
    have h1 : d.eᴴ * B.gram * d.e' = 1 := by
      have := congrArg Matrix.conjTranspose d.e'e
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_one, ← Matrix.mul_assoc] at this
    have h2 : (d.qY * a.a * Pe') p p = 1 := by
      rw [Matrix.mul_assoc, ← hE', HypDec.qY, h1, Matrix.one_apply_eq]
    rw [hQA] at h2
    simp only [Matrix.mul_apply, hPe', Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h2
    rw [mul_comm]; exact h2
  refine ⟨0, Λ.zero_mem, fun q => ∑ p, if q = (f p).rev then u q else 0, fun q => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun p _ => ?_
    split_ifs
    · exact hu q
    · exact Submodule.zero_mem _
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, hQF, zero_mulVec, zero_add,
      mulVec_mulVec, hQA, hE', Matrix.mul_assoc, ← mulVec_mulVec]
    congr 1
    funext q
    simp only [mulVec, dotProduct, Matrix.mul_apply, hPe', Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hq : q = (f p).rev
    · subst hq
      simp only [if_true, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, hS p, one_mul]
    · simp only [hq, if_false, zero_mul, Finset.sum_const_zero]

end GlobalTheory.AscFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientTraceInfinitesimal
section
noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep IsUnitEquiv)
open scoped InnerProductSpace

namespace GlobalTheory.TraceInfChar

theorem ujMat_onto {n : ℕ} {ε : Fin n → Bool} : ∀ x ∈ UJset ε, ∃ g, ujMat ε g = x := fun x hx => by
  obtain ⟨g, hg, -⟩ := GlobalTheory.RealIwasawa.exists_uMat x hx
  exact ⟨g, hg⟩

theorem isIrredOn_of_isom {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H H' : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (U : H ≃ₗᵢ[ℂ] H') (hU : ∀ g ∈ G, ∀ v, U (ρ g v) = σ g (U v)) (h : IsIrredOn G σ) : IsIrredOn G ρ := by
  intro S hS hst
  let e := U.toLinearEquiv
  have hS' : IsClosed ((S.map (e : H →ₗ[ℂ] H') : Submodule ℂ H') : Set H') := by
    rw [Submodule.map_coe]
    exact U.toHomeomorph.isClosedMap _ hS
  rcases h _ hS' (fun g hg w hw => by
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨ρ g v, hst g hg v hv, hU g hg v⟩) with h0 | h1
  · left
    rw [eq_bot_iff]
    intro v hv
    have : e v ∈ S.map (e : H →ₗ[ℂ] H') := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    have : e v ∈ S.map (e : H →ₗ[ℂ] H') := h1 ▸ Submodule.mem_top
    obtain ⟨w, hw, hwe⟩ := this
    rwa [e.injective hwe] at hw

theorem isTempered_of_unitEquiv {G V W : Type} [Group G] [MeasurableSpace G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {μ : Measure G}
    {π : G →* (V →L[ℂ] V)} {π' : G →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') (ht : GlobalTheory.Orb.IsTempered μ π) :
    GlobalTheory.Orb.IsTempered μ π' := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨v, hv, hi⟩ := ht
  refine ⟨A v, by simpa using hv, fun r hr => ?_⟩
  simpa [← hA, LinearIsometryEquiv.inner_map_map] using hi r hr

theorem hasInfChar_of_trace_ne_zero : GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.HarishChandraCharacters →
    ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
      [CompleteSpace X] (δ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (hδ : IsURepOn (UJset ε) δ),
      HasInfChar ε χ δ → ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ),
      IsPseudoCoeff (ujMat ε) μ (ujRep hδ) f → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ),
      HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 → HasInfChar ε χ π := by
  intro hL hC n ε χ X _ _ _ δ hδ hχ μ _ f hf V _ _ _ π hπ c hc hc0
  obtain ⟨b, W₀, hW₀⟩ := exists_isMinimalFlag ε
  obtain ⟨N, I, m, hstd, -, -, -, hinf, htr⟩ := hL.2.2.2.2.1 n ε b W₀ hW₀ V π hπ
  obtain ⟨-, hsum⟩ := htr μ f hf.mem
  have hcs : c = ∑ i, (m i : ℂ) * trace (repOp (I i).rep μ f) := hc.2.symm.trans hsum.2
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hcs ▸ hc0)
  have htr0 : trace (repOp (I i).rep μ f) ≠ 0 := right_ne_zero_of_mul hi
  refine (hinf i χ).1 ?_
  by_cases ha : (I i).a = 0
  · obtain ⟨hM, U, hUρ⟩ := GlobalTheory.Published.Langlands.equiv_of_zero (I i) ha
    have ht := (I i).temp
    rw [show leviOne ε (I i).W = ⊤ from hM] at ht
    obtain ⟨hσn, hσi, hσU, hσt⟩ := (isIrrTempered_top_iff μ).1 ht
    haveI := hσn
    have hAdm := (hL.1 n ε (I i)).1
    haveI hρn : Nontrivial (I i).H := U.toLinearEquiv.toEquiv.nontrivial
    have hρU : IsURepOn (UJset ε) (I i).ρ := ⟨(I i).isCRepOn, fun g hg v => by
      rw [← U.norm_map, hUρ g hg v, hσU.2.1 g hg, U.norm_map], hAdm.2.1⟩
    have hρi : IsIrredOn (UJset ε) (I i).ρ := isIrredOn_of_isom U hUρ hσi
    have hσρ : IsUnitEquiv (ujRep hσU) (ujRep hρU) :=
      ⟨U.symm, fun g v => by
        have hg : ujMat ε g ∈ UJset ε := g.2
        change U.symm ((I i).σ (ujMat ε g) v) = (I i).ρ (ujMat ε g) (U.symm v)
        apply U.injective
        rw [LinearIsometryEquiv.apply_symm_apply, hUρ _ hg, LinearIsometryEquiv.apply_symm_apply]⟩
    have hρt : GlobalTheory.Orb.IsTempered μ (ujRep hρU) := isTempered_of_unitEquiv hσρ hσt
    have hrep : (I i).rep = ujRep hρU := rfl
    have hρδ : IsUnitEquiv (ujRep hρU) (ujRep hδ) := by
      by_contra hne
      have h0 := hf.trace_other (I i).H (ujRep hρU)
        (GlobalTheory.Orb.isUnitaryRep_repVia hρU (fun g => g.2) GlobalTheory.HCChar.continuous_ujMat)
        (GlobalTheory.Orb.isTopIrreducible_repVia hρU (fun g => g.2) ujMat_onto hρi) hρt hne
      exact htr0 (hrep ▸ h0.2)
    obtain ⟨A, hA⟩ := hρδ
    refine GlobalTheory.ClassificationConsequences.hasInfChar_of_uEquiv ⟨A, fun g hg v => ?_⟩ hχ
    obtain ⟨g', rfl⟩ := ujMat_onto g hg
    exact hA g' v
  · exact absurd (GlobalTheory.T.pseudocoefficient_trace_vanishes hC n ε μ X (ujRep hδ) f hf (I i) ha).2 htr0

end GlobalTheory.TraceInfChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedHomLatticeSelf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.Twist.RatLatO

variable {D : D7}

theorem incA_eq_tmul (e : D.host.E) : incA D e = ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := rfl

theorem rat_mulVec_mem_latMul {S T : HSp D} (𝔞 : Set D.host.E) {L : Lat S} {L' : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hM : ∀ t ∈ L, M *ᵥ t ∈ L')
    {z : Fin S.rank → AE D} (hz : z ∈ GlobalTheory.FinPl.latMul S 𝔞 L P) : rat M *ᵥ z ∈ GlobalTheory.FinPl.latMul T 𝔞 L' P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, M *ᵥ s, hM s hs, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, incA_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, ← TensorProduct.tmul_sum]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem rat_mul_mem_latO : ∀ {D : D7} {S S' T T' : HSp D} {LS : Lat S} {LS' : Lat S'} {LT : Lat T} {LT' : Lat T'}, IsSelfDualC S LS → IsSelfDualC S' LS' → IsSelfDualC T' LT' → ∀ (j : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E), (∀ y ∈ LS', j *ᵥ y ∈ LS) → (∀ t ∈ LT, q *ᵥ t ∈ LT') → ∀ x : WO S T, x ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) → (rat q * x * rat j : WO S' T') ∈ latO S' T' (LS' : Set _) (LT' : Set _) (fun _ => True) := by
  intro D S S' T T' LS LS' LT LT' hS hS' hT' j q hj hq x hx
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S' T' LS' LT' hS' hT']
  refine ⟨fun i k => ?_, fun y hy => ?_⟩
  · have hxM := GlobalTheory.FinPl.LatMem.latO_mxAt hx
    simp only [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _
      (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hxM m l))
  · show (rat q * x * rat j) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : rat j *ᵥ y ∈ latV S LS (fun _ => True) :=
      rat_mulVec_mem_latMul (L := LS') (L' := LS) (P := fun _ => True) {1} j hj hy
    have h2 : x *ᵥ (rat j *ᵥ y) ∈ latA T LT (fun _ => True) := GlobalTheory.FinPl.LatMem.latO_maps hS hx h1
    exact rat_mulVec_mem_latMul (L := LT) (L' := LT') (P := fun _ => True) {a | a ∈ D.host.AA} q hq h2

end GlobalTheory.Twist.RatLatO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesLeftMulUnitaryKUInvarianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_integralMatrices_leftMul_unitary_KU_invariant : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (c : L →+* L) (r n : ℕ) (t k₁ k₂ : GU c r), k₁ ∈ KU c r → k₂ ∈ KU c r → (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1)) = (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul t.1.1)) := by
  first | exact @GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU | exact GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU | (intros; apply GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU <;> assumption)
end

