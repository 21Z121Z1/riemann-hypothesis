import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

section Volume

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def IsCMFam {I : Type} (τ : I → (E →+* ℂ)) : Prop :=
  Function.Bijective fun i => NumberField.InfinitePlace.mk (τ i)

def latC (W : HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

def StabHat (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ} (L : Set (Fin M → E))
    (m : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) : Prop :=
  ∀ y, y ∈ latHat F E L ↔ m.mulVec y ∈ latHat F E L

def IsVolMeasF (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E)
    (P Q : I → ℕ) (μ : Measure (HA (AF F) cm.sig W.gram)) : Prop :=
  μ.IsHaarMeasure ∧
  AllSome (fun θ : I → (Ainf F ⊗[F] E →+* ℂ) => ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) fun θ =>
  AllSome (fun A : ∀ ρ : I, Matrix (Fin (P ρ) ⊕ Fin (Q ρ)) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (P ρ) (Q ρ) * A ρ = W.gram.map (τ ρ)) fun A =>
  ∀ B : ∀ ρ : I, Set (UpqT (P ρ) (Q ρ)), (∀ ρ, MeasurableSet (B ρ)) →
    μ {h | StabHat F (latC W) (finMat cm.sig W.gram h) ∧
        ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat cm.sig W.gram (θ ρ) h} =
      ∏ ρ, cd.cd (P ρ) (Q ρ) (B ρ)

def VolIs (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E) (x : ℝ) : Prop :=
  AllSome (IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2)) fun μ =>
  AllSome (fun 𝓕 => IsFundamentalDomain (HFinIn (AF F) cm.sig W.gram) 𝓕 μ) fun 𝓕 =>
    μ 𝓕 = ENNReal.ofReal x

open Classical in

def trueVol (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E) : ℝ :=
  if h : ∃ x : ℝ, 0 < x ∧ VolIs cm τ cd W x then Classical.choose h else 1

theorem trueVol_pos (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E) :
    0 < trueVol cm τ cd W := by
  unfold trueVol
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact one_pos

theorem trueVol_spec (cm : CMData F E) {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E)
    (h : ∃ x : ℝ, 0 < x ∧ VolIs cm τ cd W x) : VolIs cm τ cd W (trueVol cm τ cd W) := by
  unfold trueVol
  rw [dif_pos h]
  exact (Classical.choose_spec h).2

end Volume

def CdScaleIs (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

open Classical in

def trueScale (cd : CDHaar) : ∀ n : ℕ, (Fin n → Bool) → NNReal :=
  if h : ∃ sc : ∀ n : ℕ, (Fin n → Bool) → NNReal, (∀ n ε, 0 < sc n ε) ∧ CdScaleIs cd sc then Classical.choose h
  else fun _ _ => 1

theorem trueScale_pos (cd : CDHaar) (n : ℕ) (ε : Fin n → Bool) : 0 < trueScale cd n ε := by
  unfold trueScale
  split_ifs with h
  · exact (Classical.choose_spec h).1 n ε
  · exact one_pos

def trueDsig (R : Ranks) (P : HCParam R) : ℝ := Formalism.QuantumDeterminants.fdegHC (lamSH R P)

def FiniteVolume₂ : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure →
        ∀ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → μ 𝓕 < ⊤

def DiscreteSeriesExist : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ

def FormalDegreeFormula₂ : Prop :=
  ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal), CdScaleIs cd sc →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        fdegOf ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem volTieG_iff (D : D7) : Formalism.L2.Theta.VolTieG D ↔
    ∀ W : HSpace D.host.E, W.SigOK → VolIs D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W (D.vol W) := Iff.rfl

theorem cdScaleTie_iff (D : D7) : cdScaleTie D ↔ CdScaleIs D.cd D.s.cdScale := Iff.rfl

end GlobalTheory.Mem.Vol
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.UnitarySixTwoHarishChandraParameter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Finset

namespace GlobalTheory.SignedHC.Model

def grid4 : GridData where
  k := 4
  m := 4
  t := 3
  s := 3
  ga := 9
  v := fun i => if i = 2 then 7 else if i = 3 then 3 else 4 - i
  b := fun l => 6 * l - 5
  e := fun j => 6 * j - 2
  cen := fun i => 56 - 9 * i
  two_le_k := by norm_num
  v_anti := by intro i j _ _ _; split_ifs <;> omega
  b_mono := by intro i j _ _ _; omega

theorem unitary_six_two_grid_counts : grid4.NearMid ∧
    (∀ i ∈ range 5, ∀ j ∈ range 5, IsRegular (grid4.parD i j) ∧ (grid4.parD i j).card = grid4.rankD i j ∧
      nMinus (grid4.parD i j) = (4 - j) / 2) ∧
    (∀ i ∈ range 5, IsRegular (grid4.parPi i) ∧ (grid4.parPi i).card = grid4.rankP i ∧
      nMinus (grid4.parPi i) = (4 - i + 1) / 2) ∧
    (∀ j ∈ range 5, (grid4.weightX j).card = grid4.rankX j) := by decide +kernel

theorem unitary_six_two_lift_arrows :
    (∀ i ∈ range 4, ∀ j ∈ range 5, grid4.parD (i + 1) j = liftMinus (grid4.cen (4 - i)) 3 (grid4.parD i j) ∧
      FarFrom (grid4.cen (4 - i)) 2 (grid4.parD i j)) ∧
    (∀ i ∈ range 5, ∀ j ∈ range 4, grid4.parD i (j + 1) = liftPlus (-grid4.e (j + 1)) 3 (grid4.parD i j) ∧
      FarFrom (-grid4.e (j + 1)) 3 (grid4.parD i j)) ∧
    (∀ i ∈ range 4, grid4.parPi (i + 1) = liftMinus (grid4.cen (4 - i)) 2 (grid4.parPi i) ∧
      grid4.parPi (i + 1) ≠ liftPlus (grid4.cen (4 - i)) 2 (grid4.parPi i)) ∧
    (∀ j ∈ range 4, grid4.parX (j + 1) = liftPlus (-grid4.e (j + 1)) 4 (grid4.parX j)) := by decide +kernel

theorem unitary_six_two_interlacing : ncGap grid4.lam = ((9 : ℚ) : WithTop ℚ) ∧ signature grid4.lam = (6, 2) ∧
    signature grid4.parD0 = (5, 2) ∧ HeInterlace grid4.lam grid4.parD0 ∧ ¬ HeInterlace grid4.lam (flip grid4.parD0) ∧
    ¬ HeInterlace grid4.lam (grid4.parD 0 1) ∧ ncGap (grid4.parD 2 3) = ⊤ ∧
    StrictInterlace (grid4.weightX 4) (entries (grid4.parD 4 4)) ∧
    ¬ StrictInterlace (entries (grid4.parD 4 4)) (grid4.weightX 4) := by decide +kernel

theorem he_one_one : ∀ z ∈ Icc (-6 : ℤ) 6,
    (HeInterlace {(5 / 2, true), (-3 / 2, false)} {((z : ℚ), false)} ↔ z ≤ -2) ∧
    (HeInterlace {(5 / 2, false), (-3 / 2, true)} {((z : ℚ), false)} ↔ 3 ≤ z) := by decide +kernel

theorem he_two : ∀ z ∈ Icc (-6 : ℤ) 6,
    (HeInterlace {(5 / 2, true), (-3 / 2, true)} {((z : ℚ), true)} ↔ -1 ≤ z ∧ z ≤ 2) ∧
    (StrictInterlace {5 / 2, -3 / 2} {(z : ℚ)} ↔ -1 ≤ z ∧ z ≤ 2) := by decide +kernel

theorem degenerate : ¬ StrictInterlace ∅ ∅ ∧ StrictInterlace {0} ∅ ∧ ncGap ∅ = ⊤ ∧
    ncGap {(0, true), (0, false)} = ((0 : ℚ) : WithTop ℚ) ∧ ¬ HeInterlace {(0, true), (0, false)} ∅ ∧
    ¬ HeInterlace {(1, true), (0, true)} {(0, true)} ∧ ¬ HeInterlace {(1, true), (0, true)} ∅ := by decide +kernel

theorem nMinus_parD (G : GridData) (i j : ℕ) : nMinus (G.parD i j) = (G.m - j) / 2 := by
  have : (G.parD i j).filter (fun x => x.2 = false) =
      (range ((G.m - j) / 2)).image fun a => (-(G.b (j + 2 + 2 * a) : ℚ), false) := by
    ext ⟨x, s⟩
    simp only [mem_filter, GridData.mem_parD, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨h | ⟨l, h1, h2, h3, h4⟩ | ⟨l, -, -, -, h⟩ | ⟨l, -, -, -, h⟩, rfl⟩
      · simp at h
      · have h5 : ¬ (l ≤ j + 1 ∨ Even (l - j - 1)) := by simpa using h4.symm
        rw [Nat.even_iff] at h5
        refine ⟨(l - j - 2) / 2, by omega, ?_, rfl⟩
        rw [show j + 2 + 2 * ((l - j - 2) / 2) = l by omega, h3]
      · simp at h
      · simp at h
    · rintro ⟨a, ha, rfl, rfl⟩
      refine ⟨Or.inr (Or.inl ⟨j + 2 + 2 * a, by omega, by omega, rfl, ?_⟩), rfl⟩
      symm; rw [decide_eq_false_iff_not, Nat.even_iff]; omega
  rw [nMinus, this, card_image_of_injOn, card_range]
  intro a ha a' ha' h
  simp only [coe_range, Set.mem_Iio] at ha ha'
  have h1 : G.b (j + 2 + 2 * a) = G.b (j + 2 + 2 * a') := by
    have := congrArg Prod.fst h
    simpa using this
  by_contra hne
  rcases lt_or_gt_of_ne hne with h2 | h2
  · have := G.b_mono (j + 2 + 2 * a) (j + 2 + 2 * a') (by omega) (by omega) (by omega); omega
  · have := G.b_mono (j + 2 + 2 * a') (j + 2 + 2 * a) (by omega) (by omega) (by omega); omega

theorem unitary_six_two_harish_chandra_parameter : GoodPar 8 6 2 grid4.lam := by
  refine goodPar_iff.2 ⟨⟨by decide +kernel, by decide +kernel, fun x hx => ⟨⌊x - 7 / 2⌋, ?_⟩⟩, by decide +kernel⟩
  revert x
  decide +kernel

end GlobalTheory.SignedHC.Model
end

