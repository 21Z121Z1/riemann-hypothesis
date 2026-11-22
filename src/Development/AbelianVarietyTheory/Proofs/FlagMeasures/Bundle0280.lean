import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinates
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0275
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.FrameOKMap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0277
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBigCellHaarDensityConstant
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtensionPreservesProperties
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SURestrict

variable {n : ℕ}

theorem one_mem_SUset (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  refine ⟨?_, by simp⟩
  show inUJ ε 1
  simp [inUJ]

theorem mul_mem_SUset {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ SUset ε)
    (hb : b ∈ SUset ε) : a * b ∈ SUset ε := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, by rw [Matrix.det_mul, ha2, hb2, one_mul]⟩
  have ha1' : aᴴ * Jm ε * a = Jm ε := ha1
  have hb1' : bᴴ * Jm ε * b = Jm ε := hb1
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [ha1', hb1']

theorem Kset_sub_UJset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hg
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').mp hu
  show gᴴ * Jm ε * g = Jm ε
  calc gᴴ * Jm ε * g = gᴴ * (g * Jm ε) := by rw [Matrix.mul_assoc, hc]
    _ = (star g * g) * Jm ε := by rw [← Matrix.mul_assoc]; rfl
    _ = Jm ε := by rw [h1, Matrix.one_mul]

theorem KS_sub_SUset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ KS ε) :
    g ∈ SUset ε := ⟨Kset_sub_UJset hg.1, hg.2⟩

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eq_on_SU {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (he : Ext ε m π' π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ SUset ε) : π g = π' g := by
  have := he 1 (by simp) g hg
  simpa using this

end

theorem restrict_main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (IsURepOn (UJset ε) π → IsURepOn (SUset ε) π') ∧ (IsIrredOn (UJset ε) π ↔ IsIrredOn (SUset ε) π') ∧ (∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S) ∧ ∀ v, IsKFin ε π v ↔ IsKFinS ε π' v := by
  intro n hn ε H _ _ m π' π he
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  have heq : ∀ g ∈ SUset ε, π g = π' g := fun g hg => eq_on_SU he hg
  have hSU : ∀ g ∈ SUset ε, g ∈ UJset ε := fun g hg => hg.1

  have hstab : ∀ S : Submodule ℂ H, (∀ g ∈ UJset ε, ∀ v ∈ S, π g v ∈ S) ↔
      (∀ g ∈ SUset ε, ∀ v ∈ S, π' g v ∈ S) := by
    intro S
    constructor
    · intro h g hg v hv
      rw [← heq g hg]; exact h g (hSU g hg) v hv
    · intro h g hg v hv
      obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hsplit g hg
      rw [he z hz g₀ hg₀]
      exact S.smul_mem _ (h g₀ hg₀ v hv)
  have hK : ∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S := by
    intro S
    constructor
    · intro h g hg v hv
      rw [← heq g (KS_sub_SUset hg)]; exact h g hg.1 v hv
    · intro h g hg v hv
      obtain ⟨z, hz, g₀, hg₀, rfl, hiff⟩ := hsplit g (Kset_sub_UJset hg)
      rw [he z hz g₀ hg₀]
      exact S.smul_mem _ (h g₀ (hiff.mp hg) v hv)
  refine ⟨?_, ?_, hK, ?_⟩
  · rintro ⟨⟨h1, hmul⟩, hiso, hcont⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← heq 1 (one_mem_SUset ε)]; exact h1
    · intro a ha b hb
      rw [← heq _ (mul_mem_SUset ha hb), ← heq a ha, ← heq b hb]
      exact hmul a (hSU a ha) b (hSU b hb)
    · intro g hg v
      rw [← heq g hg]; exact hiso g (hSU g hg) v
    · intro v
      exact ((hcont v).mono (fun g hg => hSU g hg)).congr (fun g hg => by simp only [heq g hg])
  · constructor
    · intro h S hS hst
      exact h S hS ((hstab S).mpr hst)
    · intro h S hS hst
      exact h S hS ((hstab S).mp hst)
  · intro v
    constructor
    · rintro ⟨S, hfd, hv, hs⟩
      exact ⟨S, hfd, hv, (hK S).mp hs⟩
    · rintro ⟨S, hfd, hv, hs⟩
      exact ⟨S, hfd, hv, (hK S).mpr hs⟩

end GlobalTheory.SURestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameMemRowLatticesOfWord
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowFrame

theorem ddIdeal_ne_bot (D : D7) :
    (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) : Ideal (𝓞 D.host.E)) ≠ ⊥ :=
  Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem one_mem_ddS_zpow_neg (D : D7) (m : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [zpow_neg, zpow_natCast, ddS, ← FractionalIdeal.coeIdeal_pow]
  refine FractionalIdeal.one_mem_inv_coe_ideal ?_
  rw [← Ideal.zero_eq_bot]
  exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact ddIdeal_ne_bot D)

theorem frame_mem_rowLat (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) (a : Fin (D.R.rS + 1)) :
    frame (lf D F0) a ∈ Λ := by
  obtain ⟨-, ⟨-, -, hz, -⟩, hX⟩ := hΛ
  have hXS : XS D F0 ≤ Λ := by
    rw [← hX]; exact inf_le_left
  induction a using Fin.lastCases with
  | last =>
    show Fin.snoc (α := fun _ => (VS D).V) F0.e F0.z (Fin.last _) ∈ Λ
    rw [Fin.snoc_last]; exact hz.1
  | cast i =>
    show Fin.snoc (α := fun _ => (VS D).V) F0.e F0.z i.castSucc ∈ Λ
    rw [Fin.snoc_castSucc]
    apply hXS
    apply Submodule.subset_span
    refine ⟨i, 1, ?_, (one_smul _ _).symm⟩
    have : -((D.R.rS : ℤ) - ((i : ℕ) : ℤ)) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub i.isLt.le]
    rw [this]
    exact one_mem_ddS_zpow_neg D _

theorem frame_mem_rows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    Λ ∈ Y.what₂ u → ∀ a, frame (lf D (X.Fu u)) a ∈ Λ :=
  fun D X Y u Λ hΛ a => frame_mem_rowLat D (X.Fu u) Λ ((Y.rowsOK u).1 Λ hΛ) a

end GlobalTheory.RowFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueFrameCongruencesUnitriangularIntegral
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameGlue

open IsDedekindDomain

theorem exists_pow_sat {R : Type*} [CommRing R] [IsDedekindDomain R] (P : HeightOneSpectrum R)
    {g : R} (hg : g ≠ 0) :
    ∃ e : ℕ, ∀ x ∈ P.asIdeal ^ e, ∃ s : R, s ∉ P.asIdeal ∧ s * x ∈ Ideal.span {g} := by
  classical
  haveI := P.isPrime
  let Rp := Localization.AtPrime P.asIdeal
  haveI : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot Rp
  have hinj : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp P.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  have hI : Ideal.map (algebraMap R Rp) (Ideal.span {g}) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ hinj).2 hg
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨n, fun x hx => ?_⟩
  have hmap : Ideal.map (algebraMap R Rp) (P.asIdeal ^ n) =
      Ideal.map (algebraMap R Rp) (Ideal.span {g}) := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow, hn]
  have hx' : algebraMap R Rp x ∈ Ideal.map (algebraMap R Rp) (Ideal.span {g}) :=
    hmap ▸ Ideal.mem_map_of_mem _ hx
  obtain ⟨⟨a, s⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff P.asIdeal.primeCompl Rp).1 hx'
  refine ⟨s, s.2, ?_⟩
  have h2 : s.1 * x = a.1 := hinj (by rw [map_mul, mul_comm]; exact h)
  rw [h2]; exact a.2

end GlobalTheory.FrameGlue

open IsDedekindDomain in
theorem GlobalTheory.FrameGlue.glue : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ), 0 < g → ∀ (f f' : Fin (r + 1) → S.V), (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, f a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, f' b - frameAct f ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ))) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, ModG S Λ g (f' b - frameAct f ξ b) := by
  intro E _ _ _ S r Λ g hg f f' hf hloc
  classical
  have hg0 : ((g : 𝓞 E)) ≠ 0 := by exact_mod_cast hg.ne'
  have hfin : {P : HeightOneSpectrum (𝓞 E) | (g : 𝓞 E) ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(g : 𝓞 E)}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg0
    · intro P hP
      exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hP)
  choose e he using fun P : HeightOneSpectrum (𝓞 E) => GlobalTheory.FrameGlue.exists_pow_sat P hg0
  let ξP : HeightOneSpectrum (𝓞 E) → Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun P =>
    if h : (g : 𝓞 E) ∈ P.asIdeal then Classical.choose (hloc P h) else 0
  have hξP : ∀ P (h : (g : 𝓞 E) ∈ P.asIdeal), ξP P = Classical.choose (hloc P h) := by
    intro P h; simp only [ξP, dif_pos h]
  have hcrt : ∀ a b : Fin (r + 1), ∃ y : 𝓞 E, ∀ P (hP : P ∈ hfin.toFinset),
      y - ξP P a b ∈ P.asIdeal ^ e P := by
    intro a b
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
      (fun P : HeightOneSpectrum (𝓞 E) => P.asIdeal) e
      (fun P _ => P.prime) (fun P _ Q _ hPQ => fun h => hPQ (HeightOneSpectrum.ext h))
      (fun P => ξP P.1 a b)
    exact ⟨y, fun P hP => hy P hP⟩
  choose y hy using hcrt
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun a b =>
    if b < a then 0 else if a = b then 1 else y a b
  refine ⟨ξ, fun a b hab => by simp [ξ, hab], fun a => by simp [ξ], fun b P hP => ?_⟩
  haveI := P.isPrime
  have hPs : P ∈ hfin.toFinset := by simpa using hP
  obtain ⟨hlow, hdiag, hmod⟩ := Classical.choose_spec (hloc P hP)
  rw [← hξP P hP] at hlow hdiag hmod

  have hdiff : ∀ a, ξP P a b - ξ a b ∈ P.asIdeal ^ e P := by
    intro a
    by_cases hba : b < a
    · simp [ξ, hba, hlow a b hba]
    · by_cases hab : a = b
      · subst hab; simp [ξ, hdiag]
      · have := hy a b P hPs
        simp only [ξ, hba, hab, if_false]
        rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 this
  set L := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) with hL
  have key : ∀ (x : 𝓞 E) (v : S.V), ((x : E)) • v = x • v := fun x v => algebraMap_smul E x v
  have hterm : ∀ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a ∈ L := by
    intro a
    obtain ⟨s, hsP, hs⟩ := he P _ (hdiff a)
    obtain ⟨t, ht, htf⟩ := hf P hP a
    refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hsP ht, ?_⟩
    have : (s * t) • (((ξP P a b - ξ a b : 𝓞 E) : E) • f a) =
        (s * (ξP P a b - ξ a b)) • (t • f a) := by
      rw [key, smul_smul, smul_smul]
      congr 1; ring
    rw [this]
    exact Submodule.smul_mem_smul hs htf
  have hsplit : f' b - frameAct f ξ b =
      (f' b - frameAct f (ξP P) b) + ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a := by
    have hs : ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a =
        frameAct f (ξP P) b - frameAct f ξ b := by
      simp only [frameAct, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast; rw [sub_smul]
    rw [hs]; abel
  rw [hsplit]
  exact L.add_mem (hmod b) (L.sum_mem fun a _ => hterm a)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GxDoubleCoset
section
open scoped Classical ComplexConjugate ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

noncomputable section

namespace GlobalTheory.GxConj

variable {r n : ℕ}

def LoUni (L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Prop :=
  (∀ a b, a < b → L a b = 0) ∧ ∀ a, L a a = 1

theorem LoUni.conj {L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : LoUni L) :
    LoUni (L.map (starRingEnd ℂ)) :=
  ⟨fun a b hab => by simp [h.1 a b hab], fun a => by simp [h.2 a]⟩

theorem sub_mul_left {l : ℕ} {ι : Type*} (hl : l ≤ r + 1) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (B : Matrix (Fin (r + 1)) ι ℂ) (c : Fin l → ι) (hA : ∀ a b, a < b → A a b = 0) :
    (A * B).submatrix (Fin.castLE hl) c =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) c := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun _ => rfl)
  intro i hi
  have hli : l ≤ i.1 := by
    by_contra hc
    exact hi ⟨⟨i.1, by omega⟩, rfl⟩
  rw [hA _ _ (by
    show a.1 < i.1
    have := a.2
    omega), zero_mul]

theorem sub_mul_right {l : ℕ} {ι : Type*} (hl : l ≤ r + 1) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (B : Matrix ι (Fin (r + 1)) ℂ) (c : Fin l → ι) (hA : ∀ a b, a < b → A a b = 0) :
    (B * Aᵀ).submatrix c (Fin.castLE hl) =
      B.submatrix c (Fin.castLE hl) * (A.submatrix (Fin.castLE hl) (Fin.castLE hl))ᵀ := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun _ => rfl)
  intro i hi
  have hli : l ≤ i.1 := by
    by_contra hc
    exact hi ⟨⟨i.1, by omega⟩, rfl⟩
  rw [hA _ _ (by
    show b.1 < i.1
    have := b.2
    omega), mul_zero]

theorem det_sub {l : ℕ} (hl : l ≤ r + 1) {L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : LoUni L) :
    (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun a _ => h.2 _
  · intro i j hij
    exact h.1 _ _ hij

theorem Dl_lo (Z P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hP : LoUni P) (hQ : LoUni Q) (l : ℕ) :
    Formalism.L2.SG.RealObj.Dl (P * Z * Qᵀ) l = Formalism.L2.SG.RealObj.Dl Z l := by
  unfold Formalism.L2.SG.RealObj.Dl
  split_ifs with h
  · rw [sub_mul_right h Q _ _ hQ.1, sub_mul_left h P _ _ hP.1, det_mul, det_mul, det_transpose,
      det_sub h hP, det_sub h hQ, one_mul, mul_one]
  · rfl

theorem Gv_lo (T T' : ℝ) (Z P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hP : LoUni P) (hQ : LoUni Q) :
    Formalism.L2.SG.RealObj.Gv T T' (P * Z * Qᵀ) = Formalism.L2.SG.RealObj.Gv T T' Z := by
  unfold Formalism.L2.SG.RealObj.Gv
  rw [Dl_lo Z P Q hP hQ, Dl_lo Z P Q hP hQ]

theorem exists_loUni (f : Fin (r + 1) → Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a, (A - 1) *ᵥ f a ∈ Submodule.span ℂ (f '' {b | b < a})) :
    ∃ L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, LoUni L ∧ ∀ a, A *ᵥ f a = ∑ c, L a c • f c := by
  have h' := fun a => (Finsupp.mem_span_image_iff_linearCombination ℂ).1 (h a)
  choose w hw hw' using h'
  have hz : ∀ a b, ¬ b < a → w a b = 0 := by
    intro a b hb
    by_contra hne
    exact hb ((Finsupp.mem_supported ℂ (w a)).1 (hw a) (Finsupp.mem_support_iff.2 hne))
  refine ⟨1 + Matrix.of fun a b => w a b, ⟨fun a b hab => ?_, fun a => ?_⟩, fun a => ?_⟩
  · rw [Matrix.add_apply, Matrix.of_apply, hz a b (not_lt_of_gt hab), Matrix.one_apply_ne (ne_of_lt hab), add_zero]
  · rw [Matrix.add_apply, Matrix.of_apply, hz a a (lt_irrefl a), Matrix.one_apply_eq, add_zero]
  · have e1 : A *ᵥ f a = f a + (A - 1) *ᵥ f a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1, ← hw' a, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp only [Matrix.add_apply, Matrix.of_apply, add_smul, Finset.sum_add_distrib, Matrix.one_apply, ite_smul,
      one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem fam_last (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : fam e z (Fin.last r) = z :=
  Fin.snoc_last (α := fun _ => Fin n → ℂ) z e

theorem fam_castSucc (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) : fam e z a.castSucc = e a :=
  Fin.snoc_castSucc (α := fun _ => Fin n → ℂ) z e a

theorem fam_span (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (h : InS e z A)
    (a : Fin (r + 1)) : (A - 1) *ᵥ fam e z a ∈ Submodule.span ℂ (fam e z '' {b | b < a}) := by
  refine Fin.lastCases ?_ (fun a => ?_) a
  · rw [fam_last]
    refine Submodule.span_mono ?_ h.2
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.castSucc, Fin.castSucc_lt_last b, fam_castSucc e z b⟩
  · rw [fam_castSucc]
    refine Submodule.span_mono ?_ (h.1 a)
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.castSucc, hb, fam_castSucc e z b⟩

theorem hJ_adj (ε : Fin n → Bool) (A Ai : Matrix (Fin n) (Fin n) ℂ)
    (hU : Aiᴴ * Formalism.REAL.Jm ε * Ai = Formalism.REAL.Jm ε) (h1 : Ai * A = 1) (x y : Fin n → ℂ) :
    hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y := by
  have e : Aiᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
    calc Aiᴴ * Formalism.REAL.Jm ε = Aiᴴ * Formalism.REAL.Jm ε * (Ai * A) := by rw [h1, Matrix.mul_one]
      _ = (Aiᴴ * Formalism.REAL.Jm ε * Ai) * A := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * A := by rw [hU]
  have e2 : Aiᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ y) = Formalism.REAL.Jm ε *ᵥ (A *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, e2]

theorem hJ_sum_left {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ c, s c • x c) y = ∑ c, conj (s c) * hJ ε (x c) y := by
  unfold hJ
  simp only [star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem hJ_sum_right {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, s c • y c) = ∑ c, s c * hJ ε x (y c) := by
  unfold hJ
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem mulVec_lin {ι : Type*} [Fintype ι] (B : Matrix (Fin n) (Fin n) ℂ) (s : ι → ℂ) (y : ι → Fin n → ℂ) :
    B *ᵥ ∑ c, s c • y c = ∑ c, s c • (B *ᵥ y c) := by
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem zhat_conj (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (A Ai B C : Matrix (Fin n) (Fin n) ℂ)
    (hadj : ∀ x y, hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y) (L M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hL : ∀ a, Ai *ᵥ f a = ∑ c, L a c • f c) (hM : ∀ b, C *ᵥ f' b = ∑ d, M b d • f' d) :
    Zhat ε f f' (A * B * C) = L.map (starRingEnd ℂ) * Zhat ε f f' B * Mᵀ := by
  ext a b
  have e1 : (A * B * C) *ᵥ f' b = A *ᵥ (B *ᵥ (C *ᵥ f' b)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  simp only [Formalism.L2.SG.RealObj.Zhat, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [e1, hadj, hL, hM, mulVec_lin, hJ_sum_left]
  simp only [hJ_sum_right, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.GxConj

namespace GlobalTheory

open GlobalTheory.GxConj

theorem gx_double_coset : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ g g' : X.B.I.Ginf), g ∈ X.SinfU u → g' ∈ X.SinfU u' → ∀ v : InfinitePlace X.B.I.F, GX X u u' 1 (g * γ * g'⁻¹) v = GX X u u' 1 γ v := by
  intro D X u u' γ g g' hg hg' v
  have hgi := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hg
  have hgi' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' hg'
  have fs : ∀ (w : D.what₂.Word), frm X w 1 v =
      fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) := by
    intro w
    funext a
    simp [frm, famSc]
  obtain ⟨L, hL, hL'⟩ := exists_loUni _ _ (fam_span _ _ _ (hgi v))
  obtain ⟨M, hM, hM'⟩ := exists_loUni _ _ (fam_span _ _ _ (hgi' v))
  have hU : (uMat (g⁻¹ v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (g⁻¹ v) = Formalism.REAL.Jm (X.B.I.ε v) := (g⁻¹ v).2
  have e : uMat ((g * γ * g'⁻¹) v) = uMat (g v) * uMat (γ v) * uMat (g'⁻¹ v) := rfl
  unfold GX ZX
  rw [fs u, fs u', e,
    zhat_conj _ _ _ _ _ _ _ (hJ_adj _ _ _ hU (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (g v))) L M hL' hM',
    Gv_lo _ _ _ _ _ hL.conj hM]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinatesStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_lie_nilpotent_coordinates : ∀ (k r : ℕ), IsHaarOn (Nset k r) (haarLie (Nset k r) 1) ∧ Set.InjOn (nCoords k r) {x | Matrix.of x ∈ Nset k r} ∧ Set.SurjOn (nCoords k r) {x | Matrix.of x ∈ Nset k r} Set.univ ∧ (haarLie (Nset k r) 1).map (nCoords k r) = (2 : ℝ≥0∞) ^ (r * (r - 1) + r * (k + 1)) • volume := by
  first | exact @GlobalTheory.SnMass.NEntry.haarLie_entries | exact GlobalTheory.SnMass.NEntry.haarLie_entries | (intros; apply GlobalTheory.SnMass.NEntry.haarLie_entries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLevelLocalDualQuotientLengthOneStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_level_local_dual_quotient_length_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 ∧ ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  first | exact @GlobalTheory.St.G.tLat_local_index | exact GlobalTheory.St.G.tLat_local_index | (intros; apply GlobalTheory.St.G.tLat_local_index <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralRowFrameMapIsometry
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameIsom

theorem frameOK_mapLF : ∀ (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
    ∀ (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂ →
    ∀ (T : D.host.E) (F : LFlag (VS D) D.R.rS T), FrameOK D Λ₁ F → FrameOK D Λ₂ (mapLF γ F) := by
  intro D γ hγ Λ₁ Λ₂ hΛ T F hF
  subst hΛ
  have e : mapLF γ F = PI.RepsIndep.Tr.mapL γ hγ F := by
    unfold mapLF
    rw [dif_pos hγ]
    rfl
  rw [e]
  exact PI.RepsIndep.Tr.FrameOK_map hγ hF

end GlobalTheory.FrameIsom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBesselCoefficientCompactLeStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_besselCoefficient_compact_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u ∈ DD σ w, AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
  first | exact @GlobalTheory.SgInf.lint_Afun_compact_le | exact GlobalTheory.SgInf.lint_Afun_compact_le | (intros; apply GlobalTheory.SgInf.lint_Afun_compact_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBigCellHaarDensityConstantStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_bigCell_haar_density_constant : ∀ (k r : ℕ) (μG μb : Measure (Mt k r)) (c cb : ℝ), 0 < c → 0 < cb → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → HasDens (Formalism.FourierDecayAlt.B2.UWb k r) μb (ENNReal.ofReal cb) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = ENNReal.ofReal (c / cb * 2 ^ r) * ∫⁻ x : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f ((Matrix.of p.1.1)⁻¹ * bigCell k r x 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂(((haarLie (Nset k r) 1).prod (haarLie (Nset k r) 1)).prod μb) := by
  first | exact @GlobalTheory.CellDens.bigCell_integral | exact GlobalTheory.CellDens.bigCell_integral | (intros; apply GlobalTheory.CellDens.bigCell_integral <;> assumption)
end

