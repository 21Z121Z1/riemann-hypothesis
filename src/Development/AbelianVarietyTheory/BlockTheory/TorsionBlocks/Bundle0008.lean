import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.HermitianLattices.Bundle0003
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.DoubleCosetDecomposition
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers

open NumberField Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem finMat_one : finMat σ J (1 : HA (AF F) σ J) = 1 := by
  show (((1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).map _ = 1
  rw [Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem finMat_mul (g h : HA (AF F) σ J) : finMat σ J (g * h) = finMat σ J g * finMat σ J h := by
  show (((HA.mat (AF F) σ J g * HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).map _ = _
  rw [Units.val_mul]
  exact Matrix.map_mul (f := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom)

def levelK (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | ∀ y, y ∈ latHat F E L ↔ (finMat σ J h).mulVec y ∈ latHat F E L}
  one_mem' := by
    intro y
    rw [finMat_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    rw [finMat_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    have := ha ((finMat σ J a⁻¹).mulVec y)
    rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec] at this
    exact this.symm

def ratPts : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

def stabAt (K : Subgroup (HA (AF F) σ J)) (g : HA (AF F) σ J) : Subgroup (HA (AF F) σ J) :=
  ratPts σ J ⊓ K.map (MulAut.conj g).toMonoidHom

def IsDoubleCosetReps (K : Subgroup (HA (AF F) σ J)) {n : ℕ} (g : Fin n → HA (AF F) σ J) : Prop :=
  ∀ x : HA (AF F) σ J, ∃! i : Fin n, ∃ γ ∈ ratPts σ J, ∃ k ∈ K, x = γ * g i * k

theorem mem_stabAt (K : Subgroup (HA (AF F) σ J)) (g γ : HA (AF F) σ J) :
    γ ∈ stabAt σ J K g ↔ γ ∈ ratPts σ J ∧ g⁻¹ * γ * g ∈ K := by
  unfold stabAt
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  rintro ⟨k, hk, rfl⟩
  simpa [mul_assoc] using hk

theorem IsDoubleCosetReps.pos {K : Subgroup (HA (AF F) σ J)} {n : ℕ} {g : Fin n → HA (AF F) σ J}
    (h : IsDoubleCosetReps σ J K g) : 0 < n := by
  obtain ⟨i, -⟩ := h 1
  exact Fin.pos i

end Level

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def latCoord (W : HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

def levelW (hc : CMData F E) (W : HSpace E) : Subgroup (HA (AF F) hc.sig W.gram) :=
  levelK hc.sig W.gram (latCoord W)

def DecompAt (hc : CMData F E) (W : HSpace E) : Prop :=
  IsOpen (levelW hc W : Set (HA (AF F) hc.sig W.gram)) ∧
  MeasurableSet (levelW hc W : Set (HA (AF F) hc.sig W.gram)) ∧
  ∃ (n : ℕ) (g : Fin n → HA (AF F) hc.sig W.gram),
    IsDoubleCosetReps hc.sig W.gram (levelW hc W) g ∧
    (∀ i, Finite (stabAt hc.sig W.gram (levelW hc W) (g i))) ∧
    ∑ i, ((Nat.card (stabAt hc.sig W.gram (levelW hc W) (g i)) : ℕ) : ℝ)⁻¹ = Formalism.HermitianLatticesTheory.mass W.hT W.L0

def IsLatticeOf (hc : CMData F E) (W : HSpace E) (g : HA (AF F) hc.sig W.gram)
    (N : Submodule (𝓞 E) W.V) : Prop :=
  ∀ x : W.V, x ∈ N ↔ ∃ y ∈ latHat F E (latCoord W),
    (finMat hc.sig W.gram g).mulVec y = fun j => inclR (Af F) (W.frame.repr x j)

open Classical in

def DecompLatAt (hc : CMData F E) (W : HSpace E) : Prop :=
  DecompAt hc W ∧
  IsCompact (levelW hc W : Set (HA (AF F) hc.sig W.gram)) ∧
  (∀ (n : ℕ) (g : Fin n → HA (AF F) hc.sig W.gram), IsDoubleCosetReps hc.sig W.gram (levelW hc W) g →
    ∃ N : Fin n → Submodule (𝓞 E) W.V,
      (∀ i, IsLatticeOf hc W (g i) (N i)) ∧ Function.Injective N ∧
      Formalism.ThetaLiftIndependence.IsClassReps W.hT W.L0 (Finset.univ.image N) ∧
      ∀ i, Finite (stabAt hc.sig W.gram (levelW hc W) (g i)) ∧ (Formalism.ThetaLiftIndependence.autL W.hT (N i)).Finite ∧
        Nat.card (stabAt hc.sig W.gram (levelW hc W) (g i)) = Nat.card (Formalism.ThetaLiftIndependence.autL W.hT (N i))) ∧
  Formalism.HermitianLatticesTheory.genus W.hT W.L0 = {N | Submodule.IsLattice E N ∧ Formalism.HermitianLatticesTheory.IsUnimodular W.hT N}

end Space

def DecompAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E), W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → DecompAt hc W

def DecompLatAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E), W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → DecompLatAt hc W

def Decomp (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → DecompAt D.sp.cm W

end GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FamilySizeBound
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FamilySizeBound

open Formalism.BasicNotions Formalism.MainNotions

def sizeAt (D : D7) (j : ℕ) (ρ : D.what₂.Tau) : ℝ := wj D (j + 1) ρ

def DataAt {D : D7} (L : SizeData₂ D) (C0 : ℝ) : Prop :=
  ∃ Δ : ℝ, StandardLattice.DataB D L.sc C0 Δ (sizeAt D)

def DataFam {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C0 x0 : ℝ, 0 < C0 ∧ ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, DataAt (Fm.L x i) C0

def Statement : Prop := ∀ (eps : ℝ) (Fm : FamP eps), DataFam Fm

end GlobalTheory.IndefiniteRowSideFullHecke.FamilySizeBound
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.VolumePerpendicular
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def IsKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.rank = M ∧ W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def IsPerp (W : HSpace E) (x : W.V) (W' : HSpace E) (ι : W'.V →ₗ[E] W.V) : Prop :=
  Function.Injective ι ∧ (∀ a b, W.hD (ι a) (ι b) = W'.hD a b) ∧
    ∀ y : W.V, (∃ a, ι a = y) ↔ W.hD y x = 0

end Spaces

def IsVol (D : D7) : letI := D.host.cmStar; HSpace D.host.E → ℕ → ℕ → ℝ → Prop :=
  letI := D.host.cmStar
  fun W P Q V =>
    0 < V ∧
    AllSome (IsVolMeas D W P Q) fun μ =>
    AllSome (fun 𝓕 => IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ) fun 𝓕 =>
      μ 𝓕 = ENNReal.ofReal V

def Concl (D : D7) : letI := D.host.cmStar;
    HSpace D.host.E → ℕ → ℕ → ℕ → D.host.E → ℕ → ℕ → Prop :=
  letI := D.host.cmStar
  fun W M P Q β P' Q' =>
    (∃ x : W.V, W.hD x x = β) ∧
    ∀ x : W.V, W.hD x x = β →
      (∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        IsPerp W x W' ι ∧ IsKind W' (M - 1) P' Q') ∧
      ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V), IsPerp W x W' ι → W'.SigOK →
        IsKind W' (M - 1) P' Q' ∧
        ∃ V V' : ℝ, IsVol D W P Q V ∧ IsVol D W' P' Q' V' ∧
          V / V' = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E M

def VolumeRatio (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (M P Q : ℕ), IsKind W M P Q → 3 ≤ M →
    (1 ≤ P → Concl D W M P Q 1 (P - 1) Q) ∧ (1 ≤ Q → Concl D W M P Q (-1) P (Q - 1))

theorem IsVol.unique (D : D7) : letI := D.host.cmStar;
    ∀ (W : HSpace D.host.E) (P Q : ℕ) (V V' : ℝ), IsVol D W P Q V → IsVol D W P Q V' → V = V' := by
  intro W P Q V V' h h'
  obtain ⟨hV, ⟨μ, hμ⟩, hall⟩ := h
  obtain ⟨hV', -, hall'⟩ := h'
  obtain ⟨⟨𝓕, h𝓕⟩, h1⟩ := hall μ hμ
  have h2 := (hall' μ hμ).2 𝓕 h𝓕
  exact (ENNReal.ofReal_eq_ofReal_iff hV.le hV'.le).1 ((h1 𝓕 h𝓕).symm.trans h2)

theorem volumeComparison_of_ratio (D : D7) (h : VolumeRatio D) (ht : VolTie D) : Conclusion2 D := by
  let _ := D.host.cmStar
  have key : ∀ (W : HSpace D.host.E) (P Q : ℕ) (β : D.host.E) (P' Q' : ℕ), W.SigOK →
      (∀ τ, W.sig τ = (P, Q)) → Concl D W W.rank P Q β P' Q' →
      ∃ x : W.V, W.hT x x = β ∧
        ∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
          HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧
          (∀ τ, W'.sig τ = (P', Q')) ∧
          D.vol W / D.vol W' = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank := by
    intro W P Q β P' Q' hs hsig hc
    obtain ⟨⟨x, hx⟩, hall⟩ := hc
    obtain ⟨⟨W', ι, hp, hk⟩, hall'⟩ := hall x hx
    obtain ⟨-, V, V', hV, hV', hr⟩ := hall' W' ι hp hk.2.1
    have e1 : V = D.vol W := IsVol.unique D W P Q _ _ hV ⟨D.vol_pos W, ht W P Q hs hsig⟩
    have e2 : V' = D.vol W' :=
      IsVol.unique D W' P' Q' _ _ hV' ⟨D.vol_pos W', ht W' P' Q' hk.2.1 hk.2.2⟩
    refine ⟨x, hx, W', ι, fun a b => hp.2.1 b a, ?_, hk.2.1, hk.2.2, by rw [← e1, ← e2, hr]⟩
    ext y
    exact hp.2.2 y
  intro W P Q hs hsig h3 s hPQ
  have hW := h W W.rank P Q ⟨rfl, hs, hsig⟩ h3
  cases s with
  | true => simpa using key W P Q 1 (P - 1) Q hs hsig (hW.1 (by simpa using hPQ))
  | false => simpa using key W P Q (-1) P (Q - 1) hs hsig (hW.2 (by simpa using hPQ))

end GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular
end
end

