import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0385
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0173
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0366
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0208
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0234

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdmissibilityWitnessesCongrModThetaLocal
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WitCong

open IsDedekindDomain Formalism.L2.SG.Pf.BBTie

theorem dvd_of_loc {E : Type} [Field E] [NumberField E] {g c : 𝓞 E} (hg : g ≠ 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∃ s, s ∉ P.asIdeal ∧ g ∣ s * c) : g ∣ c := by
  classical
  let J : Ideal (𝓞 E) := Submodule.comap (LinearMap.mulRight (𝓞 E) c) (Ideal.span {g})
  have hJ : ∀ s, s ∈ J ↔ g ∣ s * c := fun s => by
    simp [J, Submodule.mem_comap, Ideal.mem_span_singleton]
  by_contra hnd
  have hJtop : J ≠ ⊤ := by
    intro htop
    apply hnd
    have h1 : (1 : 𝓞 E) ∈ J := htop ▸ Submodule.mem_top
    simpa using (hJ 1).1 h1
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJtop
  have hgJ : g ∈ J := (hJ g).2 (dvd_mul_right g c)
  have hMbot : M ≠ ⊥ := by
    intro hb
    have hgM := hJM hgJ
    rw [hb, Ideal.mem_bot] at hgM
    exact hg hgM
  obtain ⟨s, hsP, hs⟩ := h ⟨M, hM.isPrime, hMbot⟩ (hJM hgJ)
  exact hsP (hJM ((hJ s).2 hs))

theorem coeff_dvd {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (Λ : Submodule (𝓞 E) S.V) {g : ℕ} (hg0 : g ≠ 0) (F : LFlag S r T) (hz : F.fl.z ∈ Λ)
    (hFC : IsFixedConv Λ g F) (c : Fin (r + 1) → 𝓞 E)
    (hc : ModG S Λ g (∑ a, ((c a : 𝓞 E) : E) • frame F a)) (a : Fin (r + 1)) : (g : 𝓞 E) ∣ c a := by
  classical
  have hcoe : ∀ (o : 𝓞 E) (v : S.V), o • v = (o : E) • v := fun o v => by
    rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
  have horth : ∀ v : S.V, (∀ i, S.hT (F.fl.e i) v = 0) → v ∈ orth S (Xsp F) := by
    intro v hv
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    have hle : Xsp F ≤ LinearMap.ker (S.hT.flip v) := by
      show Submodule.span E (Set.range F.fl.e) ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      simp [hv i]
    simpa using hle hx
  have hz_o : F.fl.z ∈ orth S (Xsp F) := horth _ F.fl.z_orth
  have hf_o : ∀ j, frame F j ∈ orth S (Xsp F) := by
    intro j
    induction j using Fin.lastCases with
    | last => simpa [frame, FlagG.fvec] using hz_o
    | cast i => simpa [frame, FlagG.fvec] using horth _ (fun k => F.fl.e_iso k i)
  have heX : ∀ i, F.fl.e i ∈ Xsp F := fun i => by
    show F.fl.e i ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨i, rfl⟩
  have hxdec : ∑ a, ((c a : 𝓞 E) : E) • frame F a =
      ∑ i : Fin r, ((c i.castSucc : 𝓞 E) : E) • F.fl.e i + ((c (Fin.last r) : 𝓞 E) : E) • F.fl.z := by
    rw [Fin.sum_univ_castSucc]
    simp [frame, FlagG.fvec]
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg0
  have hgcoe : ((g : 𝓞 E) : E) = (g : E) := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_natCast]
  have hgO : (g : 𝓞 E) ≠ 0 := fun h0 => hgE (by rw [← hgcoe, h0]; simp [RingOfIntegers.coe_eq_algebraMap])
  apply dvd_of_loc hgO
  intro P hgP
  haveI := P.isPrime
  obtain ⟨s, hs, hsx⟩ := hc P hgP
  have hsP : s ∉ P.asIdeal := hs
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hsx
  obtain ⟨l, hlΛ, hl⟩ := hsx
  have hlE : l = ((g : E)⁻¹ * (s : E)) • ∑ a, ((c a : 𝓞 E) : E) • frame F a := by
    have hl' : (g : E) • l = (s : E) • ∑ a, ((c a : 𝓞 E) : E) • frame F a := by
      rw [← hgcoe, ← hcoe, ← hcoe, hl]
    rw [mul_smul, ← hl', smul_smul, inv_mul_cancel₀ hgE, one_smul]
  have hlx : l = ∑ i : Fin r, ((g : E)⁻¹ * (s : E) * (c i.castSucc : E)) • F.fl.e i +
      ((g : E)⁻¹ * (s : E) * (c (Fin.last r) : E)) • F.fl.z := by
    rw [hlE, hxdec, smul_add, Finset.smul_sum]
    simp only [smul_smul]

  have hzL : ((g : E)⁻¹ * (s : E) * (c (Fin.last r) : E)) • F.fl.z ∈ Lsub Λ F := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · refine Submodule.mem_sup.2 ⟨l, ?_, -(∑ i : Fin r, ((g : E)⁻¹ * (s : E) * (c i.castSucc : E)) • F.fl.e i), ?_, ?_⟩
      · refine Submodule.mem_inf.2 ⟨hlΛ, ?_⟩
        show l ∈ orth S (Xsp F)
        rw [hlE]
        exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hf_o a))
      · show _ ∈ Xsp F
        exact neg_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (heX i))
      · rw [hlx]
        abel
    · show _ ∈ orth S (Xsp F)
      exact Submodule.smul_mem _ _ hz_o
  obtain ⟨o, ho⟩ := hFC.2 _ hzL
  induction a using Fin.lastCases with
  | last =>
    refine ⟨s, hsP, o, RingOfIntegers.ext ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast] at ho ⊢
    rw [ho]
    field_simp
  | cast j =>
    obtain ⟨cc, -, hcc1, hloc⟩ := hFC.1 P
    have hcc : ∀ i, cc i = 1 := hcc1 hgP
    set y : S.V := ∑ i : Fin r, ((g : E)⁻¹ * (s : E) * (c i.castSucc : E)) • F.fl.e i with hy
    have hyl : y = l - o • F.fl.z := by
      rw [hcoe, ho, hlx]
      abel
    have hyX : y ∈ XLam Λ F := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hyl]
        exact Submodule.sub_mem _ hlΛ (Submodule.smul_mem _ _ hz)
      · show y ∈ Xsp F
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (heX i)
    have hyloc : y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) :=
      ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hyX⟩
    rw [hloc] at hyloc
    obtain ⟨s', hs', hs'y⟩ := hyloc
    have hs'P : s' ∉ P.asIdeal := hs'
    simp only [hcc, one_smul] at hs'y
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hs'y
    have hsum : ∑ i : Fin r, ((w i : E) - (s' : E) * ((g : E)⁻¹ * (s : E) * (c i.castSucc : E))) • F.fl.e i = 0 := by
      have h1 : ∑ i : Fin r, ((w i : 𝓞 E) : E) • F.fl.e i = (s' : E) • y := by
        rw [← hcoe, ← hw]
        exact Finset.sum_congr rfl fun i _ => (hcoe _ _).symm
      simp only [sub_smul, Finset.sum_sub_distrib, h1, hy, Finset.smul_sum, smul_smul]
      exact sub_self _
    have hj := Fintype.linearIndependent_iff.1 F.fl.e_indep _ hsum j
    refine ⟨s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs'P hsP, w j, RingOfIntegers.ext ?_⟩
    rw [sub_eq_zero] at hj
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast] at hj ⊢
    rw [hj]
    field_simp

theorem wit_sub_dvd {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (Λ : Submodule (𝓞 E) S.V) {g : ℕ} (hg0 : g ≠ 0) (F : LFlag S r T) (F' : LFlag S r T') (hz : F.fl.z ∈ Λ)
    (hFC : IsFixedConv Λ g F) {ξ ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}
    (h : AdmWit Λ g F F' ξ) (h' : AdmWit Λ g F F' ξ') (a b : Fin (r + 1)) : (g : 𝓞 E) ∣ (ξ - ξ') a b := by
  have hM : ModG S Λ g (∑ c, (((ξ - ξ') c b : 𝓞 E) : E) • frame F c) := by
    have heq : ∑ c, (((ξ - ξ') c b : 𝓞 E) : E) • frame F c =
        (frame F' b - frameAct (frame F) ξ' b) - (frame F' b - frameAct (frame F) ξ b) := by
      simp only [frameAct, Matrix.sub_apply, RingOfIntegers.coe_eq_algebraMap, map_sub, sub_smul,
        Finset.sum_sub_distrib]
      abel
    rw [heq]
    intro P hP
    exact sub_mem (h'.2.2 b P hP) (h.2.2 b P hP)
  exact coeff_dvd Λ hg0 F hz hFC (fun c => (ξ - ξ') c b) hM a

theorem witness_congr : ∀ (D : D7) (Z : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), IsRowLat D F0 Λ → Formalism.L2.SG.TermDef.PD D Λ (lf D F0) u' F' → ∀ ξ ξ' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit Λ (gS D) (lf D F0) F' ξ → AdmWit Λ (gS D) (lf D F0) F' ξ' → ∀ (p : PlF D) (a b : Fin (D.R.rS + 1)), (D.s.atP p).ιE (((ξ * ξ'⁻¹) a b : 𝓞 D.host.E) : D.host.E) - (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))} := by
  intro D Z u u' F0 Λ F' hR _hPD ξ ξ' hξ hξ' p a b
  obtain ⟨-, hFH, -⟩ := hR
  obtain ⟨-, -, hL, hFC⟩ := hFH
  have hg0 : gS D ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hdiff : ∀ c d, ((gS D : ℕ) : 𝓞 D.host.E) ∣ (ξ - ξ') c d :=
    fun c d => wit_sub_dvd Λ hg0 (lf D F0) F' hL.1 hFC hξ hξ' c d
  have hdet : IsUnit ξ'.det := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => hξ'.1 i j hji)]
    simp [hξ'.2.1]
  have hkey : ξ * ξ'⁻¹ - 1 = (ξ - ξ') * ξ'⁻¹ := by
    rw [Matrix.sub_mul, Matrix.mul_nonsing_inv _ hdet]
  have hdvd : ((gS D : ℕ) : 𝓞 D.host.E) ∣ (ξ * ξ'⁻¹ - 1) a b := by
    rw [hkey, Matrix.mul_apply]
    exact Finset.dvd_sum fun c _ => (hdiff a c).mul_right _
  obtain ⟨y, hy⟩ := hdvd
  have hsub : (D.s.atP p).ιE (((ξ * ξ'⁻¹) a b : 𝓞 D.host.E) : D.host.E) -
      (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b =
      ((gS D : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E) := by
    have h1 : (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b =
        (D.s.atP p).ιE (((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) a b : 𝓞 D.host.E) :
          D.host.E) := by
      by_cases h : a = b <;> simp [Matrix.one_apply, h, RingOfIntegers.coe_eq_algebraMap]
    have h2 : (ξ * ξ'⁻¹) a b = (ξ * ξ'⁻¹ - 1) a b + (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1))
        (𝓞 D.host.E)) a b := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [h1, h2, hy]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_natCast, add_sub_cancel_right]
  obtain ⟨-, -, -, hO, -, hsp⟩ := Z.agree p
  have hyO : (D.s.atP p).ιE (y : D.host.E) ∈ (Z.M p).L.O := by
    rw [hO, (D.s.atP p).O_def]
    exact IsIntegral.tower_top ((RingOfIntegers.isIntegral_coe y).map (D.s.atP p).ιE.toIntAlgHom)
  have hgO : ((gS D : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E) ∈ (Z.M p).L.O :=
    mul_mem (natCast_mem _ _) hyO
  rw [hsub]
  unfold Formalism.MainNotions.S.LocNG.theta
  revert hsp
  cases hM : (Z.M p).split with
  | none =>
    intro _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hgO⟩, ?_⟩
    simp [Subring.smul_def]
  | some gM =>
    cases hD : (D.s.atP p).split with
    | none =>
      intro h
      exact h.elim
    | some sg =>
      rintro ⟨-, hq⟩
      have hl := (D.s_split p).1 (by rw [hD]; rfl)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      have hθ : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gM.q : (D.s.atP p).Fp) =
          ((Formalism.MainNotions.S.Loc.resChar p : ℕ) : (D.s.atP p).Ep) := by
        rw [hq, sg.q_eq, map_natCast]
      rw [hθ]
      rcases hl with hl | hl
      · refine Submodule.mem_span_singleton.2
          ⟨⟨((D.host.g 1 : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E),
            mul_mem (natCast_mem _ _) hyO⟩, ?_⟩
        rw [Subring.smul_def, smul_eq_mul, hl]
        simp only [gS, Nat.cast_mul]
        ring
      · refine Submodule.mem_span_singleton.2
          ⟨⟨((D.host.g 0 : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E),
            mul_mem (natCast_mem _ _) hyO⟩, ?_⟩
        rw [Subring.smul_def, smul_eq_mul, hl]
        simp only [gS, Nat.cast_mul]
        ring

end GlobalTheory.WitCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationDegenerateSidePieceBound
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.DegSide

variable {k r : ℕ}

theorem measurableSet_GG : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  simpa [Set.compl_setOf] using (WUnfold.measurableSet_not_GG (k := k) (r := r)).compl

theorem measurable_indicator_GG {β : Type} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [Zero β]
    {f : Mat k r → β} (hf : ContinuousOn f (GG k r)) :
    Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => f (Matrix.of x)) := by
  classical
  have h : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} := hf
  have := h.measurable_piecewise (g := fun _ => (0 : β)) continuousOn_const measurableSet_GG
  rwa [← Set.piecewise_eq_indicator]

theorem measurable_mulP : Measurable fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := by
  have : Continuous fun p : Mat k r × Mat k r => p.1 * p.2 := continuous_fst.matrix_mul continuous_snd
  have h : Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := this
  exact h.measurable

theorem measurable_conjM (h : Mat k r) : Measurable (conjM h : Mt k r → Mt k r) := by
  have : Continuous fun x : Mat k r => h * x * h⁻¹ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h' : Continuous (conjM h : Mt k r → Mt k r) := this
  exact h'.measurable

theorem null_of_fibres {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN ν : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN) (hq : IsQuotMeas μG (muProd μW μN) ν)
    {A : Set (Mt k r)} (hA : MeasurableSet A) (h0 : ∀ g : Mat k r, μN (rmulM g ⁻¹' A) = 0) : μG A = 0 := by
  haveI := hN.1
  have hconj : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN :=
    (GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW μN hz hT hW hN).2.2.2.2
  have hm : Measurable (A.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, hq _ hm]
  refine (lintegral_congr fun x => ?_).trans lintegral_zero
  have hx : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  show ∫⁻ s, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) ∂(muProd μW μN) = 0
  unfold muProd
  rw [lintegral_map hx measurable_mulP, lintegral_prod (fun p : Mt k r × Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of p.1) p.2)))
      (hx.comp measurable_mulP).aemeasurable]
  have haeW : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := hW.2.2.1
  refine (lintegral_congr_ae (haeW.mono fun h hh => ?_)).trans lintegral_zero
  have hg : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of h * Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  have e : ∀ n : Mt k r, rmulM (Matrix.of x) (lmulM (Matrix.of h) n) =
      rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n) := by
    intro n
    show (Matrix.of h * Matrix.of n * Matrix.of x : Mat k r) =
      Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
    rw [Matrix.mul_assoc (Matrix.of h * Matrix.of n : Mat k r),
      Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hh.1)]
  show ∫⁻ n, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of h) n)) ∂μN = 0
  simp only [e]
  rw [← lintegral_map hg (measurable_conjM _), hconj _ hh, ← h0 (Matrix.of h * Matrix.of x),
    ← lintegral_indicator_one ((continuous_rmulM _).measurable hA)]
  rfl

theorem mem_Sset_of_mem_Nset (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg2_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {s x : Mat k r}
    (hs : s ∈ Sset k r z) (hx : x ∈ GG k r) : Sg2 k r z (s * x) = Sg2 k r z x := by
  have := (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.1 x hx s hs 1 ⟨isClosedSub_GG.2.2.1, one_mem _⟩
  rwa [Matrix.mul_one] at this

theorem tail {Wq : Type} [NormedAddCommGroup Wq] {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {ν : Measure (Mt k r)} {Φ : Mat k r → Wq} {q : ℕ} {H₁ : ℝ} (hH : 1 ≤ H₁) (ht : TailBd z ν Φ q H₁) (i : ℕ)
    {Q : Set (Mt k r)} (hQ : MeasurableSet Q) (hsub : ∀ x ∈ Q, i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z (Matrix.of x)) :
    ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤
      ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG ν Φ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine (setLIntegral_le_lintegral _ _).trans (le_mul_of_one_le_left zero_le ?_)
    rw [ENNReal.one_le_ofReal]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one]
    linarith
  · have h2 : (0 : ℝ) < 2 ^ i := by positivity
    have h := ht (2 ^ i) h2
    have e : 2 * (2 * r + 2 : ℝ) * (2 ^ i : ℝ) ^ (-(2 * (q : ℝ))) = (4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹ := by
      rw [Real.rpow_neg h2.le, ← Real.rpow_natCast (2 ^ i : ℝ) (2 * q)]
      push_cast
      ring
    rw [e] at h
    refine le_trans ?_ h
    rw [← lintegral_indicator hQ]
    refine lintegral_mono (Set.indicator_le_indicator_of_subset (fun x hx => ?_) fun _ => zero_le)
    have hx' := (hsub x hx).resolve_left hi.ne'
    have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
    rcases ((GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.2.2 (Matrix.of x)).2.2.2 with h' | ⟨a, ha⟩
    · exfalso
      rw [h'] at hx'
      nlinarith
    · exact ⟨a, ha ▸ hx'.le⟩

theorem side_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yj k r hj z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset0 k r hj z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol0 k r j R₀ De y * ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  intro k r j hj z z' Wq _ _ _ π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hjk hκ hs hH hO ht hDe hNR hqR
  have hO' := hO
  obtain ⟨hz', hT', hnt, hπ, -, hG, hW, -, hN, hqS, hψ, hΦ, hΦc, hc, hl2⟩ := hO'
  have hz := hNR.1
  have hT := hNR.2.2.1
  obtain ⟨hγ, hRc, hRh, hRu, -⟩ := GlobalTheory.T.stabilizer_measure_normalisation_symm k r j hj z z' γ s μR hs hNR
  obtain ⟨hoff, hnull, φ, hφ, hcut⟩ := GlobalTheory.T.cutoff_computes_besselQuotientIntegral k r _ μG μR νR hRc hG hRh hRu hqR
  have hV := GlobalTheory.T.fibreVolume_normalFormStabiliser k r j hj z z' γ De s μR hj1 hjk hDe hs hNR
  obtain ⟨hYm, hEm⟩ := GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' γ hz hz' hT hT' hγ
  have hYi : ∀ ρ ∈ Rset k r γ, ∀ x ∈ GG k r, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x :=
    fun ρ hρ x hx => (GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' γ hz hz' hγ x hx).2.2 ρ hρ
  have hmul : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := isClosedSub_GG.2.2.2.1
  refine ⟨?_, fun w hw i R₀ y hR hy => ?_⟩
  · set A : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (Matrix.of x) = 0} with hAdef
    have hA : MeasurableSet A := by
      have := measurableSet_GG.inter (hYm (measurableSet_singleton 0))
      convert this using 1
      ext x
      refine and_congr_right fun hx => ?_
      rw [Set.mem_preimage, Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
      rfl
    have hA0 : μG A = 0 := by
      refine null_of_fibres hz' hT' hW hN hqS hA fun g => ?_
      by_cases hg : g ∈ GG k r
      · rw [Measure.smul_apply, measure_mono_null (t := {n | Yj k r hj z z' γ (Matrix.of n * g) = 0}) (fun n hn => hn.2)
          (hV g hg).1, smul_zero]
      · refine measure_mono_null (t := {x | Matrix.of x ∉ Nset k r}) (fun n hn hn' => hg ?_) hN.2.2.1
        exact (WUnfold.mul_mem_GG_iff hn'.1).1 hn.1
    have hA1 : νR A = 0 := by
      refine hnull A hA (fun ρ hρ x hx => ?_) hA0
      show (ρ * Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (ρ * Matrix.of x) = 0) ↔ (_ ∧ _)
      rw [hYi ρ hρ _ hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hoff hA1)
    by_cases hx' : Matrix.of x ∈ GG k r
    · exact Or.inr ⟨hx', hx.resolve_left (not_not.2 hx')⟩
    · exact Or.inl hx'
  · set E := Eset0 k r hj z z' γ R₀ y with hE
    set Q : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x))} with hQdef
    have hQ : MeasurableSet Q := by
      have h1 := measurable_indicator_GG (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' hz' hT').2.2.1
      have h2 := measurableSet_GG.inter ((MeasurableSet.const (i = 0)).union (measurableSet_lt
        (measurable_const (a := 2 ^ i * H₁)) h1))
      convert h2 using 1
      ext x
      refine and_congr_right fun hx => ?_
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rw [Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
    have hEQ : E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)} = E ∩ Q := by
      ext x
      exact and_congr_right fun hx => ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩
    have hQi : ∀ s ∈ Sset k r z', ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q) := by
      intro s hs x hx
      show (s * Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (s * Matrix.of x))) ↔ (_ ∧ _)
      rw [Sg2_left hz' hT' hs hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ (WUnfold.Sset_subset _ hs) _ hx, h.2⟩⟩
    have hEi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ E ↔ x ∈ E) := by
      intro ρ hρ x hx
      show (ρ * Matrix.of x ∈ GG k r ∧ Sg2 k r z' (ρ * Matrix.of x) ≤ R₀ ∧ Sg2 k r z (γ * (ρ * Matrix.of x)) ≤ R₀ ∧
        y < Yj k r hj z z' γ (ρ * Matrix.of x) ∧ Yj k r hj z z' γ (ρ * Matrix.of x) ≤ 2 * y) ↔ (_ ∧ _)
      have e : γ * (ρ * Matrix.of x) = γ * ρ * γ⁻¹ * (γ * Matrix.of x) := by
        rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hγ), Matrix.mul_assoc]
      rw [hYi ρ hρ _ hx, Sg2_left hz' hT' (mem_Sset_of_mem_Nset _ hρ.1) hx, e,
        Sg2_left hz hT (mem_Sset_of_mem_Nset _ hρ.2) (hmul _ hγ _ hx)]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    set g : Mt k r → ℝ≥0∞ := fun x => (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 with hg
    have hgi : ∀ ρ ∈ Nset k r, ∀ x, Matrix.of x ∈ GG k r → g (lmulM ρ x) = g x := by
      intro ρ hρ x hx
      have h1 := hΦ 1 (isClosedSub_UWset z').2.2.1 ρ hρ _ hx
      rw [Matrix.one_mul, hπ.1.1] at h1
      have h2 : ‖ψ' ρ‖₊ = 1 := NNReal.eq (hψ ρ hρ)
      show (‖⟪w, Φ' (ρ * Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 = _
      rw [h1, inner_smul_right, nnnorm_mul, h2, one_mul]
      rfl
    have hFm : Measurable ((E ∩ Q).indicator g) := by
      have h1 : ContinuousOn (fun x : Mat k r => (‖⟪w, Φ' x⟫_ℂ‖₊ : ℝ≥0∞) ^ 2) (GG k r) :=
        (ENNReal.continuous_pow 2).comp_continuousOn
          (ENNReal.continuous_coe.comp_continuousOn (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const hΦc).nnnorm)
      have h2 := (measurable_indicator_GG h1).indicator ((hEm R₀ y).inter hQ)
      rwa [Set.indicator_indicator, Set.inter_eq_left.2 (fun x hx => hx.2.1)] at h2
    have hFi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r →
        (E ∩ Q).indicator g (lmulM ρ x) = (E ∩ Q).indicator g x := by
      intro ρ hρ x hx
      have hiff : lmulM ρ x ∈ E ∩ Q ↔ x ∈ E ∩ Q :=
        and_congr (hEi ρ hρ x hx) (hQi ρ (mem_Sset_of_mem_Nset _ hρ.1) x hx)
      by_cases h : x ∈ E ∩ Q
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.2 h), hgi ρ hρ.1 x hx]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.1 h)]
    have hP := GlobalTheory.T.amplitude_one_side_unfolding k r z' π' ψ' μG μW' _ νS' Φ' c hO (fun x => φ x * E.indicator 1 x) Q
      (ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s))
      (hφ.1.mul (measurable_one.indicator (hEm R₀ y))) hQ hQi (fun g hg => by
        rw [lintegral_smul_measure, smul_eq_mul]
        exact mul_le_mul_right ((hV g hg).2 φ hφ R₀ y hR hy) _) w hw
    have hTl := tail hz' hT' hH ht i hQ fun x hx => hx.2
    have hfib : 0 ≤ fibVol0 k r j R₀ De y := by
      have := hDe.1
      unfold fibVol0
      positivity
    have hd : (0 : ℝ) < Module.finrank ℂ Wq := Nat.cast_pos.2 Module.finrank_pos
    calc ∫⁻ x in E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)},
          ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR
        = ∫⁻ x, (E ∩ Q).indicator g x ∂νR := by
          rw [hEQ, lintegral_indicator ((hEm R₀ y).inter hQ)]
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
          rfl
      _ = ∫⁻ x in Q, φ x * E.indicator 1 x * g x ∂μG := by
          rw [hcut _ hFm hFi, ← lintegral_indicator hQ]
          refine lintegral_congr fun x => ?_
          by_cases h1 : x ∈ E <;> by_cases h2 : x ∈ Q <;> simp [h1, h2]
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s) * (Module.finrank ℂ Wq : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS' Φ') :=
          hP.trans (mul_le_mul_right hTl _)
      _ = _ := by
          rw [hl2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hd, ← ENNReal.ofReal_mul hκ.le,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp

end GlobalTheory.Amp.DegSide
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatchStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnDictionary_bijective_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictBij X Tr hK := by
  first | exact @GlobalTheory.St.colDict_bij_of_levelMatch | exact GlobalTheory.St.colDict_bij_of_levelMatch | (intros; apply GlobalTheory.St.colDict_bij_of_levelMatch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibreStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure ∧ ((fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT)) {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y} = 0 ∧ ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∀ s : (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y) → s y • ratTup (Fv F v) (F0 P) = y) → ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ0 ∂(fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT))) := by
  first | exact @GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser | exact GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser | (intros; apply GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermUnitaryMoveLocalTermStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTerm_unitary_move_localTerm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) (r : ℕ) (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r), Formalism.MainNotions.S.LocNG.IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) := by
  first | exact @GlobalTheory.LocOver.isTerm_unitary_move | exact GlobalTheory.LocOver.isTerm_unitary_move | (intros; apply GlobalTheory.LocOver.isTerm_unitary_move <;> assumption)
end

