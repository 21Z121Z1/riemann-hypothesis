import Mathlib
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ColumnStabiliser
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      Subgroup (GL (Fin D.R.k) D.host.E) :=
  letI := D.host.cmStar
  fun y =>
    UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ⊓
      ((Lv u).U.comap (MulAut.conj (y : GL (Fin D.R.k)
          (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))⁻¹).toMonoidHom).comap
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))

theorem mem_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ (y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (γ : GL (Fin D.R.k) D.host.E),
      γ ∈ colStab D Lv u y ↔
        γ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ∧
          (y : GL (Fin D.R.k) _)⁻¹ *
            bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
            (y : GL (Fin D.R.k) _) ∈ (Lv u).U := by
  intro y γ
  simp [colStab, Subgroup.mem_inf, Subgroup.mem_comap]

def ColStabTrivialAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      colStab D Lv u y = ⊥

def ColStabTrivial : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), ColStabTrivialAt D Lv u

example (D : D7) : GBig D ↔ ∃ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i := by
  unfold GBig
  exact exists_congr fun i => by omega

example (h : ColStabTrivial) (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (hg : GBig D)
    (hs : ∀ i : Fin 2, SplitsF D (D.host.g i)) (c : (D.mem u).C.cls 0)
    (γ : (D.mem u).C.stab 0 c) : γ = 1 := by
  let _ := D.host.cmStar
  have hb := h D Lv u hg hs ((Lv u).y c)
  have hr := ((Lv u).stabI_range c ((Lv u).stabI c γ).1 ((Lv u).stabI c γ).2).1 ⟨γ, rfl⟩
  have hm : ((Lv u).stabI c γ).1 ∈ colStab D Lv u ((Lv u).y c) := by
    rw [mem_colStab]
    refine ⟨((Lv u).stabI c γ).2, ?_⟩
    obtain ⟨x, hx, hx'⟩ := hr
    rw [← hx']
    simpa [mul_assoc] using hx
  rw [hb, Subgroup.mem_bot] at hm
  apply (Lv u).stabI_inj c
  rw [map_one]
  exact Subtype.ext hm

theorem map_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (colStab D Lv u y).map (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) =
        ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
          (Lv u).U.map (MulAut.conj (y : GL (Fin D.R.k) _)).toMonoidHom := by
  intro y
  ext x
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_colStab D Lv u y γ).1 hγ
    exact ⟨⟨γ, h1, rfl⟩, ⟨_, h2, by simp [mul_assoc]⟩⟩
  · rintro ⟨⟨γ, h1, rfl⟩, z, hz, hz'⟩
    refine ⟨γ, (mem_colStab D Lv u y γ).2 ⟨h1, ?_⟩, rfl⟩
    rw [← hz']
    simpa [mul_assoc] using hz

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped ENNReal TensorProduct

abbrev RightCosets {G' G : Type} [Group G'] [Group G] (j : G' →* G) : Type :=
  Quotient (QuotientGroup.rightRel j.range)

def IsQuotientMeasure {G' G : Type} [Group G'] [Group G] [MeasurableSpace G'] [MeasurableSpace G]
    (j : G' →* G) (m' : Measure G') (m : Measure G) (ν : Measure (RightCosets j)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂m = ∫⁻ c, ∫⁻ g', f (j g' * Quotient.out c) ∂m' ∂ν

def IsStabEmb {P' Q' P Q : ℕ} (x₀ : Fin P ⊕ Fin Q → ℂ) (j : UpqT P' Q' →* UpqT P Q) : Prop :=
  ∃ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ,
    Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' ∧
    (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x₀ = 0 ∧
    ∀ g' : UpqT P' Q', UpqT.mat (j g') *ᵥ x₀ = x₀ ∧ UpqT.mat (j g') * C = C * UpqT.mat g'

def piEmb {T : Type} {P' Q' P Q : ℕ} (j : T → (UpqT P' Q' →* UpqT P Q)) :
    (T → UpqT P' Q') →* (T → UpqT P Q) where
  toFun g ρ := j ρ (g ρ)
  map_one' := by funext ρ; simp
  map_mul' g h := by funext ρ; simp

def infCoord {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M P Q : ℕ}
    (θ : Ainf F ⊗[F] E →+* ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ)
    (Y : Fin 1 → Fin M → Ainf F ⊗[F] E) : Fin P ⊕ Fin Q → ℂ :=
  A *ᵥ fun i => θ (Y 0 i)

def phiLat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (latHat F E L : Set (Fin M → Af F ⊗[F] E)).indicator 1 (projFin X 0) * Φi (projInf X)

def atInv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) : ℝ≥0∞ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) x)

def coordTup {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) (x : W.V) :
    Fin 1 → Fin W.rank → E :=
  fun _ i => W.frame.repr x i

def UnfoldAt (D : D7) : letI := D.host.cmStar;
    ∀ (W W' : HSpace D.host.E) (_P _Q _P' _Q' : ℕ) (_β : D.host.E) (_x : W.V), Prop :=
  letI := D.host.cmStar
  fun W W' P Q P' Q' β x =>
  ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram))
    (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsVolMeas D W P Q μ → IsVolMeas D W' P' Q' μ' →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
    μ 𝓕 < ⊤ → μ' 𝓕' < ⊤ →
    AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
      ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
    AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
      ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
    AllSome (fun j : D.what₂.Tau → (UpqT P' Q' →* UpqT P Q) =>
      ∀ ρ, IsStabEmb (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) (j ρ)) fun j =>
    AllSome (IsQuotientMeasure (piEmb j) (Measure.pi fun _ => D.cd.cd P' Q')
      (Measure.pi fun _ => D.cd.cd P Q)) fun ν =>
    AllSome (fun pt : (D.what₂.Tau → UpqT P Q) →
        (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
      ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) =
        UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i))) fun pt =>
    ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
      ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = β},
          atInv D.sp.cm.sig W.gram (phiLat (L0c D W) Φi) h (coordTup W x'.1) ∂μ =
        μ' 𝓕' * ∫⁻ c, Φi (pt (Quotient.out c)) ∂ν

def Unfolding (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∀ x : W.V, W.hT x x = (if s then 1 else -1) → x ∈ W.L0 →
    ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
      HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
      (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) →
      (∀ y, y ∈ W'.L0 ↔ ι y ∈ W.L0) →
      UnfoldAt D W W' P Q (if s then P - 1 else P) (if s then Q else Q - 1) (if s then 1 else -1) x

def UnfoldingAnyLattice (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∀ x : W.V, W.hT x x = (if s then 1 else -1) → x ∈ W.L0 →
    ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
      HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
      (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) →
      UnfoldAt D W W' P Q (if s then P - 1 else P) (if s then Q else Q - 1) (if s then 1 else -1) x

theorem IsStabEmb.inv_mul_fix {P' Q' P Q : ℕ} {x₀ : Fin P ⊕ Fin Q → ℂ} {j : UpqT P' Q' →* UpqT P Q}
    (hj : IsStabEmb x₀ j) (g' : UpqT P' Q') (g : UpqT P Q) :
    UpqT.mat (j g' * g)⁻¹ *ᵥ x₀ = UpqT.mat g⁻¹ *ᵥ x₀ := by
  obtain ⟨C, -, -, h⟩ := hj
  have h1 := (h g'⁻¹).1
  have e : UpqT.mat (j g' * g)⁻¹ = UpqT.mat g⁻¹ * UpqT.mat (j g'⁻¹) := by
    rw [_root_.mul_inv_rev, ← map_inv]; rfl
  rw [e, ← Matrix.mulVec_mulVec, h1]

example (P Q : ℕ) : IsStabEmb (0 : Fin P ⊕ Fin Q → ℂ) (MonoidHom.id (UpqT P Q)) :=
  ⟨1, by simp, by simp, fun g => ⟨by simp, by simp⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
section
open MvPolynomial NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

def brOne (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)).toLinearMap ∘ₗ
    (VV K fun _ : Unit => sg).subtype ∘ₗ
      Br.brStdP (K := K) hN (fun _ : Unit => lam) (fun _ : Unit => sg) ∘ₗ
        (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))).toLinearMap

theorem brOne_rename (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : VV K fun _ : Unit => lam) :
    brOne K hN lam sg (rename Prod.snd (G : Pol K Unit N)) =
      rename Prod.snd ((Br.brStd hN (fun _ : Unit => lam) (fun _ : Unit => sg) G : VV K fun _ : Unit => sg) : Pol K Unit n) := by
  have h : rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))
      (rename Prod.snd (G : Pol K Unit N)) = (G : Pol K Unit N) := by
    rw [rename_rename]
    exact rename_id_apply _
  simp only [brOne, Br.brStd, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h, Submodule.subtype_apply]

theorem interlace_iff {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.Interlace hN lam sg ↔ Formalism.MainNotions.PrimeDegreeVariant.Interlace hN.symm lam sg := by
  refine forall_congr' fun i => ?_
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC]
  omega

def OnePlace : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
      Formalism.MainNotions.PrimeDegreeVariant.IsBr hN.symm lam sg (brOne ℂ hN lam sg)

def Equivariance : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → Br.BrEquiv K hN lam sg

def Integrality : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrIntegral K hN lam sg

def Homogeneity : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ t : ι → Kˣ,
      Br.brStd hN lam sg ∘ₗ (rhoK lam fun τ => (Formalism.MainNotions.PrimeDegreeVariant.lastGL K N (t τ))⁻¹) = Br.brAt hN lam sg (fun τ => (t τ : K)) ∧
      Br.brAt hN lam sg (fun τ => (t τ : K)) =
        ((∏ τ, t τ ^ (-((∑ i, (lam τ).w i) - ∑ i, (sg τ).w i)) : Kˣ) : K) • Br.brStd hN lam sg

def Members : Prop :=
  ∀ (X : Fields) (Word : Type) (R : Ranks) (W : Wts X Word R), W.Ok → ∀ (u : Word) (τ : X.Tau),
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) ∧ Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)

def Statement : Prop := OnePlace ∧ Equivariance ∧ Integrality ∧ Homogeneity ∧ Members

def Transposed : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
      ∃ io, Formalism.MainNotions.PrimeDegreeVariant.IsIota hN.symm lam sg io ∧ Formalism.MainNotions.PrimeDegreeVariant.IsTranspose lam sg io (brOne ℂ hN lam sg)

def Tensor : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ (f : ι → MvPolynomial (Fin N × Fin N) K) (G : VV K lam), (∀ τ, f τ ∈ nablaSq K N (lam τ)) → (G : Pol K ι N) = ten f →
      ((Br.brStd hN lam sg G : VV K sg) : Pol K ι n) = ten fun τ => brOne K hN (lam τ) (sg τ) (f τ)

def BaseChange : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] (φ : K →+* K') (N n : ℕ) (hN : N = n + 1)
    (lam : DomWeight N) (sg : DomWeight n), Br.Interlace hN lam sg → Br.SameShift lam sg →
    ∀ f ∈ nablaSq K N lam, brOne K' hN lam sg (map φ f) = map φ (brOne K hN lam sg f)

def iotaNormSq {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  ((Formalism.MainNotions.PrimeDegreeVariant.cBr hN.symm lam sg : ℤ) : ℝ) ^ 2 *
    (normFock lam (Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg) (Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg)).re

def ExactNorm : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
      (∀ a : ℂˣ, IsGreatest
        {r : ℝ | ∃ f ∈ delSq ℂ N lam,
          (normFock lam (sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ N a) f) (sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ N a) f)).re = 1 ∧
          r = (normFock sg (brOne ℂ hN lam sg f) (brOne ℂ hN lam sg f)).re}
        ((‖(a : ℂ)‖ ^ 2) ^ (-Br.nBr lam sg) * iotaNormSq hN lam sg)) ∧
      iotaNormSq hN lam sg ≤ Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm lam sg ^ 2 ∧
      (Br.d0 hN lam sg = 0 → iotaNormSq hN lam sg = 1)

def StatementSharp : Prop := Statement ∧ Transposed ∧ Tensor ∧ BaseChange ∧ ExactNorm

theorem brAt_eq {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (t : ι → Kˣ) :
    Br.brAt hN lam sg (fun τ => (t τ : K)) =
      ((∏ τ, t τ ^ (-((∑ i, (lam τ).w i) - ∑ i, (sg τ).w i)) : Kˣ) : K) • Br.brStd hN lam sg := by
  simp [Br.brAt, Br.nBr]

theorem members_sameShift {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (hW : W.Ok) (u : Word) (τ : X.Tau) :
    Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ) :=
  (lamTrue_sgTrue_detShift W hW u τ).symm

example : ∃ (lam : DomWeight 3) (sg : DomWeight 2),
    Br.Interlace (by rfl : 3 = 2 + 1) lam sg ∧ Br.SameShift lam sg ∧ Br.d0 (by rfl : 3 = 2 + 1) lam sg = 1 := by
  refine ⟨⟨![2, 0, -1], by decide⟩, ⟨![1, -1], by decide⟩, ?_, ?_, ?_⟩
  · unfold Br.Interlace; decide
  · unfold Br.SameShift; decide
  · decide

end GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IsometryTransportFrames
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def HasSig (W : HSpace E) (P Q : ℕ) : Prop := W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def withLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : HSpace E :=
  { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hU }

def frameMat (W₁ W₂ : HSpace E) (e : W₁.V →ₗ[E] W₂.V) : Matrix (Fin W₂.rank) (Fin W₁.rank) E :=
  LinearMap.toMatrix W₁.frame W₂.frame e

def CarriesLat (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop := ∀ x : W₁.V, x ∈ W₁.L0 ↔ e x ∈ W₂.L0

example (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : (withLat W L hL hU).gram = W.gram := rfl

example (W : HSpace E) : withLat W W.L0 W.standardTuple_isLattice W.baseLattice_isUnimodular = W := rfl

example (W₁ W₂ : HSpace E) (e : W₁.V →ₗ[E] W₂.V) (x : W₁.V) :
    (frameMat W₁ W₂ e).mulVec (W₁.frame.repr x) = W₂.frame.repr (e x) :=
  LinearMap.toMatrix_mulVec_repr _ _ _ _

end Spaces

def IsConjBy {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ}
    (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E) (T : Matrix (Fin M₂) (Fin M₁) E)
    (φ : HA (AF F) σ J₁ → HA (AF F) σ J₂) : Prop :=
  ∀ h : HA (AF F) σ J₁,
    ((HA.mat (AF F) σ J₂ (φ h) : GL (Fin M₂) (AF F ⊗[F] E)) : Matrix (Fin M₂) (Fin M₂) (AF F ⊗[F] E)) *
        T.map (inclR (F := F) (AF F)) =
      T.map (inclR (F := F) (AF F)) *
        ((HA.mat (AF F) σ J₁ h : GL (Fin M₁) (AF F ⊗[F] E)) : Matrix (Fin M₁) (Fin M₁) (AF F ⊗[F] E))

def LatticeIndep (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), HasSig W P Q →
    ∀ (L : Submodule (𝓞 D.host.E) W.V) (hL : Submodule.IsLattice D.host.E L)
      (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)),
      IsVolMeas D W P Q μ ↔ IsVolMeas D (withLat W L hL hU) P Q μ

def IsometryTransport (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → CarriesLat W₁ W₂ e →
      ∃ φ : HA (AF D.host.F) D.sp.cm.sig W₁.gram ≃ₜ* HA (AF D.host.F) D.sp.cm.sig W₂.gram,
        IsConjBy D.sp.cm.sig W₁.gram W₂.gram (frameMat W₁ W₂ e.toLinearMap) φ ∧
        (∀ h, h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram ↔
          φ h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) ∧
        (∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
          IsVolMeas D W₁ P Q μ ↔ IsVolMeas D W₂ P Q (μ.map φ)) ∧
        (∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram))
            (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W₁.gram)),
          IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram) 𝓕 μ ↔
            IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) (φ '' 𝓕) (μ.map φ))

def VolEqOfIsometric (D : D7) : Prop :=
  letI := D.host.cmStar
  VolTie D → ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → D.vol W₁ = D.vol W₂

def VolIndep (D : D7) : Prop := LatticeIndep D ∧ IsometryTransport D ∧ VolEqOfIsometric D

end GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.OnePlaceBranchStatement
section
open NumberField MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OnePlaceBranching

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

def brOne (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  (rename (R := K) (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)).toLinearMap ∘ₗ
    (VV K fun _ : Unit => sg).subtype ∘ₗ
      Br.brStdP (K := K) hN (fun _ : Unit => lam) (fun _ : Unit => sg) ∘ₗ
        (rename (R := K) (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))).toLinearMap

def OnePlaceIsBr : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
    Formalism.MainNotions.PrimeDegreeVariant.IsBr hN.symm lam sg (brOne ℂ hN lam sg)

def OnePlaceTranspose : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
    ∃ io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      Formalism.MainNotions.PrimeDegreeVariant.IsIota hN.symm lam sg io ∧ Formalism.MainNotions.PrimeDegreeVariant.IsTranspose lam sg io (brOne ℂ hN lam sg)

def IsTensor : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ (f : ι → MvPolynomial (Fin N × Fin N) K), (∀ τ, f τ ∈ nablaSq K N (lam τ)) →
      ∀ G : VV K lam, (G : Pol K ι N) = ten f →
        ((Br.brStd hN lam sg G : VV K sg) : Pol K ι n) = ten fun τ => brOne K hN (lam τ) (sg τ) (f τ)

def EquivNe : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) →
    Br.BrEquiv K hN lam sg ∧ ((∀ τ, Br.SameShift (lam τ) (sg τ)) → Br.brStd (K := K) hN lam sg ≠ 0)

def Integral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrIntegral K hN lam sg

def Homogeneous : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ (t : ι → Kˣ) (G : VV K lam),
      Br.brAt hN lam sg (fun τ => (t τ : K)) G =
        Br.brStd hN lam sg (rhoK lam (fun τ => Formalism.MainNotions.PrimeDegreeVariant.lastGL K N (t τ))⁻¹ G) ∧
      Br.brAt hN lam sg (fun τ => (t τ : K)) G =
        (∏ τ, (t τ : K) ^ (-((∑ i, (lam τ).w i) - ∑ i, (sg τ).w i))) • Br.brStd hN lam sg G

def MemberWeights : Prop :=
  ∀ (X : Fields) (Word : Type) (R : Ranks) (W : Wts X Word R), W.Ok → ∀ (u : Word) (τ : X.Tau),
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) ∧
    Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)

def Statement : Prop :=
  OnePlaceIsBr ∧ OnePlaceTranspose ∧ IsTensor ∧ EquivNe ∧ Integral ∧ Homogeneous ∧ MemberWeights

theorem interlace_iff {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.Interlace hN lam sg ↔ Formalism.MainNotions.PrimeDegreeVariant.Interlace hN.symm lam sg := by
  refine forall_congr' fun i => ?_
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, sub_nonneg]
  exact and_comm

def lamEx : DomWeight 3 := ⟨![3, 1, 1], by decide⟩

def sgEx : DomWeight 2 := ⟨![2, 1], by decide⟩

example : Br.Interlace (N := 3) (n := 2) rfl lamEx sgEx ∧ Br.SameShift lamEx sgEx ∧
    Br.d0 (N := 3) (n := 2) rfl lamEx sgEx = 1 ∧ lamEx.detShift = 1 := by
  refine ⟨?_, rfl, ?_, rfl⟩
  · intro i
    fin_cases i <;> simp [Br.aBr, Br.bBr, Br.iS, Br.iC, lamEx, sgEx]
  · simp [Br.d0, Br.aBr, Br.iS, lamEx, sgEx, Fin.sum_univ_two]

end GlobalTheory.IndefiniteRowSideFullHecke.OnePlaceBranching
end
end

