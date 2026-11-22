import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.HeckeOrthSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

open Module.End
open scoped InnerProductSpace

variable {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem iSup_iInf_eigenspace_eq_top [FiniteDimensional ℂ E] (T : I → E →ₗ[ℂ] E) (hc : ∀ i k, Commute (T i) (T k))
    (hadj : ∀ i, ∃ k, ∀ x y, ⟪T i x, y⟫_ℂ = ⟪x, T k y⟫_ℂ) :
    ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) = ⊤ := by
  choose s hs using hadj
  have hs' : ∀ i x y, ⟪T (s i) x, y⟫_ℂ = ⟪x, T i y⟫_ℂ := fun i x y => by
    rw [← inner_conj_symm, ← hs, inner_conj_symm]
  let H : I ⊕ I → E →ₗ[ℂ] E := Sum.elim (fun i => T i + T (s i)) (fun i => Complex.I • (T i - T (s i)))
  have hH : ∀ i, (H i).IsSymmetric := by
    rintro (i | i) x y
    · simp only [H, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right, hs i, hs' i]
      ring
    · simp only [H, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, hs i, hs' i, Complex.conj_I]
      ring
  have hT : ∀ i k, Commute (H i) (T k) := by
    rintro (i | i) k
    · exact (hc _ _).add_left (hc _ _)
    · exact ((hc _ _).sub_left (hc _ _)).smul_left _
  have hHc : ∀ i k, Commute (H i) (H k) := by
    rintro i (k | k)
    · exact (hT _ _).add_right (hT _ _)
    · exact ((hT _ _).sub_right (hT _ _)).smul_right _
  have h := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hH (fun i k _ => hHc i k)
  rw [eq_top_iff, ← h]
  refine iSup_le fun χ => le_iSup_of_le (fun i => (χ (.inl i) - Complex.I * χ (.inr i)) / 2) fun x hx => ?_
  simp only [Submodule.mem_iInf, mem_eigenspace_iff] at hx ⊢
  intro i
  have h1 : T i x + T (s i) x = χ (.inl i) • x := hx (.inl i)
  have h2 : Complex.I • (T i x - T (s i) x) = χ (.inr i) • x := hx (.inr i)
  have h3 : T i x - T (s i) x = -(Complex.I * χ (.inr i)) • x := by
    rw [neg_smul, mul_smul, ← h2, smul_smul, Complex.I_mul_I]; simp
  have h4 : (2 : ℂ) • T i x = (χ (.inl i) - Complex.I * χ (.inr i)) • x := by
    rw [sub_eq_add_neg, add_smul, ← h1, ← h3, two_smul]; abel
  rw [div_eq_inv_mul, mul_smul, ← h4, smul_smul]; simp

end Abstract

section Form

variable {X I : Type} [AddCommGroup X] [Module ℂ X]

structure IsPosOn (Y : Submodule ℂ X) (B : X → X → ℂ) : Prop where
  lin : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z
  symm : ∀ x ∈ Y, ∀ y ∈ Y, B y x = star (B x y)
  pos : ∀ x ∈ Y, x ≠ 0 → 0 < (B x x).re

example : IsPosOn (⊤ : Submodule ℂ ℂ) (fun x y => star x * y) where
  lin x _ y _ z _ c := by simp only [smul_eq_mul]; ring
  symm x _ y _ := by simp [mul_comm]
  pos x _ hx := by
    have : star x * x = (Complex.normSq x : ℂ) := by rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [this]; exact Complex.normSq_pos.2 hx

variable {Y : Submodule ℂ X} {B : X → X → ℂ}

theorem IsPosOn.zero_right (h : IsPosOn Y B) {x : X} (hx : x ∈ Y) : B x 0 = 0 := by
  have := h.lin x hx 0 Y.zero_mem 0 Y.zero_mem 1
  simpa using this

theorem IsPosOn.add_right (h : IsPosOn Y B) {x y z : X} (hx : x ∈ Y) (hy : y ∈ Y) (hz : z ∈ Y) :
    B x (y + z) = B x y + B x z := by
  simpa using h.lin x hx y hy z hz 1

theorem IsPosOn.smul_right (h : IsPosOn Y B) {x z : X} (hx : x ∈ Y) (hz : z ∈ Y) (c : ℂ) :
    B x (c • z) = c * B x z := by
  simpa [h.zero_right hx] using h.lin x hx 0 Y.zero_mem z hz c

@[reducible] def IsPosOn.core (h : IsPosOn Y B) : InnerProductSpace.Core ℂ Y where
  inner x y := B x y
  conj_inner_symm x y := (h.symm y y.2 x x.2).symm
  re_inner_nonneg x := by
    by_cases hx : (x : X) = 0
    · show 0 ≤ (B x x).re
      rw [hx, h.zero_right Y.zero_mem]; simp
    · exact (h.pos x x.2 hx).le
  add_left x y z := by
    show B ((x : X) + y) z = B x z + B y z
    rw [h.symm z z.2 _ (Y.add_mem x.2 y.2), h.add_right z.2 x.2 y.2, h.symm z z.2 x x.2, h.symm z z.2 y y.2, star_add]
  smul_left x y r := by
    show B (r • (x : X)) y = starRingEnd ℂ r * B x y
    rw [h.symm y y.2 _ (Y.smul_mem r x.2), h.smul_right y.2 x.2, h.symm y y.2 x x.2, star_mul']
    rfl
  definite x hx := by
    by_contra h0
    have := h.pos x x.2 (fun e => h0 (Subtype.ext e))
    have hx' : B x x = 0 := hx
    rw [hx'] at this
    simp at this

theorem IsPosOn.le_iSup_eigen [FiniteDimensional ℂ Y] (h : IsPosOn Y B) (T : I → X →ₗ[ℂ] X)
    (hT : ∀ i, ∀ x ∈ Y, T i x ∈ Y) (hc : ∀ i k, ∀ x ∈ Y, T i (T k x) = T k (T i x))
    (hadj : ∀ i, ∃ k, ∀ x ∈ Y, ∀ y ∈ Y, B (T i x) y = B x (T k y))
    (Z : Submodule ℂ X) (hZ : ∀ (χ : I → ℂ), ∀ x ∈ Y, (∀ i, T i x = χ i • x) → x ∈ Z) : Y ≤ Z := by
  letI := h.core
  letI : NormedAddCommGroup Y := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ Y := InnerProductSpace.ofCore _
  have key := iSup_iInf_eigenspace_eq_top (E := Y) (fun i => (T i).restrict (hT i))
    (fun i k => LinearMap.ext fun x => Subtype.ext (hc i k x x.2))
    (fun i => (hadj i).imp fun k hk x y => hk x x.2 y y.2)
  have : (⊤ : Submodule ℂ Y) ≤ Z.comap Y.subtype := by
    rw [← key]
    refine iSup_le fun χ x hx => hZ χ x x.2 fun i => ?_
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx
    exact congrArg Subtype.val (hx i)
  exact fun x hx => this (x := ⟨x, hx⟩) Submodule.mem_top

theorem IsPosOn.iSupIndep (h : IsPosOn Y B) (part : I → Submodule ℂ X) (hle : ∀ i, part i ≤ Y)
    (horth : ∀ i k, i ≠ k → ∀ x ∈ part i, ∀ y ∈ part k, B x y = 0) : iSupIndep part := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  by_contra h0
  have h1 := h.pos x (hle i hx) h0
  have h2 : ∀ y ∈ ⨆ k, ⨆ (_ : k ≠ i), part k, y ∈ Y ∧ B x y = 0 := by
    intro y hy
    refine Submodule.iSup_induction (motive := fun y => y ∈ Y ∧ B x y = 0) _ hy ?_ ⟨Y.zero_mem, h.zero_right (hle i hx)⟩ ?_
    · intro k y hy
      by_cases hk : k = i
      · simp only [hk, ne_eq, not_true_eq_false, iSup_neg, not_false_eq_true, Submodule.mem_bot] at hy
        rw [hy]; exact ⟨Y.zero_mem, h.zero_right (hle i hx)⟩
      · rw [iSup_pos hk] at hy
        exact ⟨hle k hy, horth i k (Ne.symm hk) x hx y hy⟩
    · intro y z hy hz
      exact ⟨Y.add_mem hy.1 hz.1, by rw [h.add_right (hle i hx) hy.1 hz.1, hy.2, hz.2, add_zero]⟩
  rw [(h2 x hx').2] at h1
  simp at h1

end Form

section Local

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
  (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))

def KeepsAt : Prop :=
  ∀ P d R, Hecke₂ V J χ Sb P d R → ∀ T ∈ goodPart θ M J χ e, heckeOn M R T ∈ goodPart θ M J χ e

def CommuteAt : Prop :=
  ∀ P d R P' d' R', Hecke₂ V J χ Sb P d R → Hecke₂ V J χ Sb P' d' R' →
    ∀ T ∈ goodPart θ M J χ e, heckeOn M R (heckeOn M R' T) = heckeOn M R' (heckeOn M R T)

def AdjointAt : Prop :=
  ∀ P d R, Hecke₂ V J χ Sb P d R → (∃ R', Hecke₂ V J χ Sb P (dualLab d) R') ∧
    ∀ R', Hecke₂ V J χ Sb P (dualLab d) R' →
      ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
        ∀ T ∈ goodPart θ M J χ e, ∀ T' ∈ goodPart θ M J χ e,
          ipM M μ 𝓕 (heckeOn M R T) T' = ipM M μ 𝓕 T (heckeOn M R' T')

def SchurAt : Prop := ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurMult θ M J χ μ 𝓕

def FiniteAt : Prop := FiniteDimensional ℂ (goodPart θ M J χ e)

variable {θ V S M J χ Sb e}

theorem exists_haar (V : HSp D) : ∃ μ : Measure (GA D V), μ.IsHaarMeasure := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact ⟨Measure.haar, inferInstance⟩

end Local

open GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading

def AtLifts (D : D7)
    (Φ : (D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) → ∀ (V : HSp D) (S : D.what₂.Tau → SPar), DSModel V S →
      Set (GA D V) → (GA D V → ℂ) → Finset (HeightOneSpectrum (𝓞 D.host.F)) → ((GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) → Prop) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (pb : Fin 2 → 𝓞 D.host.E) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), Lev.IsTypePlaces D.host.g pb Pg →
  ∀ (pl : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq D.host ≃ ↥Pg), IsPlaceMatch pl →
  ∀ (red : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
    (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.IsGeneratorFamily (H := D.host) om →
  ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBadSet D Sb →
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m →
  ∀ (hj : (D.sp.W j).rank = D.R.r) (M : ModelW D j) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W j) β →
    Φ θ (D.sp.W j) _ M (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
      (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) Sb (eGoodOp (D.sp.W j) hj β ψ pl red om)

def HeckeKeeps (D : D7) : Prop := AtLifts D KeepsAt

def HeckeCommute (D : D7) : Prop := AtLifts D CommuteAt

def HeckeAdjoint (D : D7) : Prop := AtLifts D AdjointAt

def PeterssonExists (D : D7) : Prop := AtLifts D fun θ V S M J χ _ _ => SchurAt θ V S M J χ

def GoodFinite (D : D7) : Prop := AtLifts D fun θ V S M J χ _ e => FiniteAt θ V S M J χ e

def LabelsAgree (D : D7) : Prop :=
  ∀ (pb : Fin 2 → 𝓞 D.host.E) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), Lev.IsTypePlaces D.host.g pb Pg →
  ∀ (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBadSet D Sb →
  ∀ (βm : GL (Fin (D.sp.W D.R.m).rank) (Lev.EAf D)), IsFrameAtG (D.sp.W D.R.m) βm →
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m →
  ∀ (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)), IsFrameAtG (D.sp.W j) β →
  ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ),
    (∃ R, Hecke₂ (D.sp.W j) (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
      (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) Sb P d R) ↔
    (∃ R, Hecke₂ (D.sp.W D.R.m) (Lev.levG (D.sp.W D.R.m) βm (levelDatumAtBasePrime (D.sp.W D.R.m) Pg ψ) : Set (GA D (D.sp.W D.R.m)))
      (Lev.levChi (D.sp.W D.R.m) βm (levelDatumAtBasePrime (D.sp.W D.R.m) Pg ψ)) Sb P d R)

def PartsOccur (D : D7) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (pb : Fin 2 → 𝓞 D.host.E) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), Lev.IsTypePlaces D.host.g pb Pg →
  ∀ (pl : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq D.host ≃ ↥Pg), IsPlaceMatch pl →
  ∀ (red : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
    (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.IsGeneratorFamily (H := D.host) om →
  ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBadSet D Sb →
  ∀ (hm : (D.sp.W D.R.m).rank = D.R.r) (Mm : ModelW D D.R.m) (βm : GL (Fin (D.sp.W D.R.m).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W D.R.m) βm →
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m →
  ∀ (hj : (D.sp.W j).rank = D.R.r) (M : ModelW D j) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W j) β →
  ∀ c : EigSys D, partW θ j hj M β ψ pl red om Sb c ≠ ⊥ → partW θ D.R.m hm Mm βm ψ pl red om Sb c ≠ ⊥

end GlobalTheory.HeckeOrthSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisAltTail
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusEndChar

theorem main : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (f : G ⟶ G), IsMonHom f → letI := E.addCommGroup; ∃! ρ : E.X →+ E.X, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ f ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ χ) := by
  intro k _ G _ _ E f hf
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  haveI : IsMonHom E.q := E.q_hom
  haveI : IsMonHom E.i := E.i_hom
  haveI : IsProper E.B.hom := E.isAbelian.proper
  haveI : ConnectedSpace (Sp k) := by
    have : PreconnectedSpace (PrimeSpectrum k) := by
      refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint k) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
      exact (IsLocalRing.specializes_closedPoint y).mem_closure
    exact (⟨inferInstance⟩ : ConnectedSpace (PrimeSpectrum k))
  have hk : E.i ≫ f ≫ E.q = toUnit _ ≫ η[E.B] :=
    splitTorus_hom_proper_trivial_local k E.X E.B (E.i ≫ f ≫ E.q) inferInstance
  let τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X :=
    E.isKernel.lift (E.i ≫ f) (toUnit _) (by rw [Category.assoc, hk])
  have hτ : τ ≫ E.i = E.i ≫ f := E.isKernel.lift_fst _ _ _
  have hmono : Mono E.i := E.isKernel.mono_fst_of_mono
  have hτm : IsMonHom τ := by
    constructor
    · rw [← cancel_mono E.i, Category.assoc, hτ, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono E.i, Category.assoc, Category.assoc, hτ, IsMonHom.mul_hom_assoc (f := E.i),
        IsMonHom.mul_hom (f := f), IsMonHom.mul_hom (f := E.i), tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hτ]
  obtain ⟨ρ, hρ⟩ := SplitTorusHom.exists_addMonoidHom (S := Sp k) τ
  refine ⟨ρ, ⟨τ, hτ, fun χ => Units.ext ?_⟩, ?_⟩
  · rw [chV_val, hρ]
  · rintro ρ' ⟨τ', hτ', hρ'⟩
    have hττ : τ' = τ := by rw [← cancel_mono E.i, hτ', hτ]
    subst hττ
    ext χ
    apply SplitTorusHom.charUnit_injective (S := Sp k)
    rw [← hρ', chV_val, hρ]

end GlobalTheory.TorusEndChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InTypeIsoSortedPos
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace GlobalTheory.InertTypeIso

open Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : Ideal (𝓞 E))

def consEquiv (a : ℕ) (s : List ℕ) :
    inType P (a :: s) ≃ₗ[𝓞 E] (𝓞 E ⧸ P ^ a) × inType P s where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons (α := fun i : Fin (s.length + 1) => 𝓞 E ⧸ P ^ (a :: s).get i) p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨u, v⟩
    rfl

def zeroEquiv (s : List ℕ) : inType P (0 :: s) ≃ₗ[𝓞 E] inType P s :=
  haveI : Subsingleton (𝓞 E ⧸ P ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr ((pow_zero P).trans Ideal.one_eq_top)
  (consEquiv P 0 s).trans
    { toFun := Prod.snd
      invFun := fun x => (0, x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ => rfl }

theorem iso_of_perm {s t : List ℕ} (h : s.Perm t) :
    Nonempty (inType P s ≃ₗ[𝓞 E] inType P t) := by
  induction h with
  | nil => exact ⟨LinearEquiv.refl _ _⟩
  | cons a _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨(consEquiv P a _).trans (((LinearEquiv.refl _ _).prodCongr e).trans (consEquiv P a _).symm)⟩
  | swap a b l =>
    exact ⟨(consEquiv P b _).trans <|
      ((LinearEquiv.refl _ _).prodCongr (consEquiv P a l)).trans <|
      (LinearEquiv.prodAssoc _ _ _ _).symm.trans <|
      ((LinearEquiv.prodComm _ _ _).prodCongr (LinearEquiv.refl _ _)).trans <|
      (LinearEquiv.prodAssoc _ _ _ _).trans <|
      ((LinearEquiv.refl _ _).prodCongr (consEquiv P b l).symm).trans (consEquiv P a _).symm⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨e1.trans e2⟩

theorem iso_filter_pos (s : List ℕ) :
    Nonempty (inType P s ≃ₗ[𝓞 E] inType P (s.filter (fun a => 0 < a))) := by
  induction s with
  | nil => exact ⟨LinearEquiv.refl _ _⟩
  | cons a s ih =>
    obtain ⟨e⟩ := ih
    cases a with
    | zero =>
      have hf : (0 :: s).filter (fun a => 0 < a) = s.filter (fun a => 0 < a) := by simp
      rw [hf]
      exact ⟨(zeroEquiv P s).trans e⟩
    | succ m =>
      have hf : ((m + 1) :: s).filter (fun a => 0 < a) = (m + 1) :: s.filter (fun a => 0 < a) := by
        simp
      rw [hf]
      exact ⟨(consEquiv P _ s).trans (((LinearEquiv.refl _ _).prodCongr e).trans (consEquiv P _ _).symm)⟩

theorem inType_iso_sorted_pos : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : Ideal (𝓞 E)) (s : List ℕ),
    ∃ y : List ℕ, y.Pairwise (· ≥ ·) ∧ (∀ a ∈ y, 0 < a) ∧ Nonempty (inType P s ≃ₗ[𝓞 E] inType P y) := by
  intro E _ _ _ P s
  refine ⟨(s.filter (fun a => 0 < a)).insertionSort (· ≥ ·), List.pairwise_insertionSort _ _, ?_, ?_⟩
  · intro a ha
    have := ((List.perm_insertionSort (· ≥ ·) _).mem_iff).mp ha
    simpa using (List.mem_filter.mp this).2
  · obtain ⟨e1⟩ := iso_filter_pos P s
    obtain ⟨e2⟩ := iso_of_perm P (List.perm_insertionSort (· ≥ ·) (s.filter (fun a => 0 < a))).symm
    exact ⟨e1.trans e2⟩

end GlobalTheory.InertTypeIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFlatPointAtGenericPoints
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem injective_of_flat_of_range_subset_genericPoints :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (X : Scheme.{0}) (s : X ⟶ Sp R) (x : Sp K ⟶ X) (β : R →+* K), Flat s → Set.range x ⊆ genericPoints X → x ≫ s = spMap β → Function.Injective β := by
  intro R K _ _ _ X s x β hs hx hxs
  set pt : Sp K := IsLocalRing.closedPoint K with hpt
  have hp : x pt ∈ genericPoints X := hx ⟨_, rfl⟩
  let g₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hg₀ : g₀ ⤳ s (x pt) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s hg₀
  have h₁ : closure ({x pt} : Set X) ⊆ closure {y} :=
    specializes_iff_closure_subset.mp hy
  have h₂ : closure ({y} : Set X) ⊆ closure {x pt} :=
    hp.2 isIrreducible_singleton.closure h₁
  have hyx : y = x pt :=
    (hy.antisymm (specializes_iff_closure_subset.mpr h₂)).eq
  have h₃ : (x ≫ s) pt = g₀ := by
    rw [Scheme.Hom.comp_apply, ← hyx, e]
  rw [hxs] at h₃
  have h₄ : (spMap β pt).asIdeal = RingHom.ker β := by
    show Ideal.comap β (IsLocalRing.maximalIdeal K) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  rw [h₃] at h₄
  exact (RingHom.injective_iff_ker_eq_bot β).mpr h₄.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBasOfPreimageEq
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isBas_of_preimage_eq (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i] (C : Type)
    [Category.{0} C] (V : C → X.Opens) (V₀ : C → X₀.Opens) (hV : ∀ T, i ⁻¹ᵁ V T = V₀ T) (h : IsBas V₀) :
    IsBas V := by
  have hle : ∀ (t : C) (U : X.Opens), V₀ t ≤ i ⁻¹ᵁ U → V t ≤ U := by
    intro t U htU z hz
    obtain ⟨w, rfl⟩ := i.surjective z
    have hw : w ∈ V₀ t := by rw [← hV t]; exact hz
    exact htU hw
  have hmem : ∀ (t : C) (y : X₀), y ∈ V₀ t → i y ∈ V t := by
    intro t y hy
    rw [← hV t] at hy
    exact hy
  have hmem' : ∀ (t : C) (y : X₀), i y ∈ V t → y ∈ V₀ t := by
    intro t y hy
    rw [← hV t]
    exact hy
  refine ⟨fun x U hx ↦ ?_, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t, hyt, htU⟩ := h.1 y (i ⁻¹ᵁ U) hx
    exact ⟨t, hmem t y hyt, hle t U htU⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t₃, a₁, a₂, hy₃, h₃U⟩ := h.2 t₁ t₂ y (i ⁻¹ᵁ U) hx (hmem' t₁ y h₁) (hmem' t₂ y h₂)
    exact ⟨t₃, a₁, a₂, hmem t₃ y hy₃, hle t₃ U h₃U⟩

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDetStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kroneckerProductFamily_mul_one_det : ∀ (T : Type) [Fintype T] [DecidableEq T] (J : T → Type) [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] (R : Type) [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R), kron M * kron M' = kron (fun t => M t * M' t) ∧ kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 ∧ (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  first | exact @GlobalTheory.DefPt.kronFamily_mul_one_det | exact GlobalTheory.DefPt.kronFamily_mul_one_det | (intros; apply GlobalTheory.DefPt.kronFamily_mul_one_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastRowTopComponentDualWeylEqMonomialMulStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_top_component_dualWeyl_eq_monomial_mul : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (G : BP K n), G ∈ dualWeyl K (n + 1) n lam → ∀ b : Fin n → ℕ, (∀ s, b s ≤ lam s) → (∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg fun s => (b s : ℤ)) → ∃ f ∈ dualWeyl K n n (fun s => lam s - b s), zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  first | exact @GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb | exact GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb | (intros; apply GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb <;> assumption)
end

