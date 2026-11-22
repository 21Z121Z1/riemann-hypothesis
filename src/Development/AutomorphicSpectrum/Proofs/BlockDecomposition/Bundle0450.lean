import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Fib

section Abstract

variable {G D W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddGroup D] [TopologicalSpace D] [IsTopologicalAddGroup D]
  [AddCommGroup W] [Module ℂ W]

theorem isLocallyConstant_translate (H : Subgroup G) (σ : Representation ℂ H W)
    (f : smoothPart (ind H σ)) (e : D → G) (he : Continuous e) (h0 : e 0 = 1)
    (hadd : ∀ a b, e (a + b) = e a * e b) (y : G) :
    IsLocallyConstant (fun d => f.1.1 (e d * y)) := by
  have hK : IsOpen {g : G | ind H σ g f.1 = f.1} := f.2
  let c : D → G := fun a => y⁻¹ * e a * y
  have hc : Continuous c := by fun_prop
  have hU : IsOpen (c ⁻¹' {g : G | ind H σ g f.1 = f.1}) := hK.preimage hc
  rw [IsLocallyConstant.iff_exists_open]
  intro d
  refine ⟨(fun x => -d + x) ⁻¹' (c ⁻¹' {g : G | ind H σ g f.1 = f.1}), hU.preimage (by fun_prop), ?_, ?_⟩
  · show ind H σ (c (-d + d)) f.1 = f.1
    simp [c, h0]
  · intro x hx
    have hx' : ind H σ (c (-d + x)) f.1 = f.1 := hx
    have h1 : e x = e d * e (-d + x) := by rw [← hadd, add_neg_cancel_left]
    have h2 := congrArg (fun v : indSpace H σ => v.1 (e d * y)) hx'
    have h3 : (ind H σ (c (-d + x)) f.1).1 (e d * y) = f.1.1 (e d * y * c (-d + x)) := rfl
    simp only [h3] at h2
    have h4 : e d * y * c (-d + x) = e x * y := by
      simp only [c, h1]; group
    simpa [h4] using h2

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp [dEmb, this]

theorem dEmb_add (i t : ℕ) (a b : Fin (t + 1) → k) : dEmb k i t (a + b) = dEmb k i t a * dEmb k i t b := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (a + b) = Fin.append (0 : Fin (i + 1) → k) a + Fin.append (0 : Fin (i + 1) → k) b := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp only [dEmb, Subgroup.coe_mul, this, ofAdd_add, map_mul]

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  have hcol : Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
    refine continuous_matrix fun r c => ?_
    by_cases hc : c = Fin.last _
    · subst hc
      refine Fin.lastCases ?_ (fun r' => ?_) r
      · simpa [colMat] using continuous_const
      · simp only [colMat, if_true, Fin.lastCases_castSucc]
        refine Fin.addCases (fun a => ?_) (fun a => ?_) r'
        · simpa using continuous_const
        · simpa using continuous_apply a
    · simpa [colMat, hc] using continuous_const
  constructor
  · exact continuous_const.add hcol
  · exact continuous_const.sub hcol

theorem dEmb_mul_entry (i t : ℕ) (d : Fin (t + 1) → k) (g : Mir k ((i + 1) + t + 1)) (b : Fin (t + 1)) :
    (((dEmb k i t d * g : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) =
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) + d b := by
  have hg : ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.last _) (Fin.last _) = 1 := by
    have := congrFun ((mem_Mir_iff k _).1 g.2) (Fin.last _)
    simpa [eLast] using this
  have hv : ((dEmb k i t d : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k).val =
      1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := rfl
  have hc : colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = d b := by
    simp only [colMat, if_true, Fin.lastCases_castSucc, Fin.append_right]
  rw [Subgroup.coe_mul, Units.val_mul, hv, add_mul, one_mul, Matrix.add_apply, mul_apply,
    Finset.sum_eq_single (Fin.last _)]
  · rw [hc]
    exact congrArg (_ + ·) ((congrArg (d b * ·) hg).trans (mul_one _))
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem hpg_entry_eq_zero (i t : ℕ) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (b : Fin (t + 1)) :
    ((h : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = 0 := by
  have h1 := mem_parab_iff.1 (show ((h : GL (Fin ((i + 1) + (t + 1) + 1)) k)) ∈ parab k (ePG (i + 1) (t + 1)) from hh)
    true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_false_last] at h1
  have h2 : ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) := by
    apply Fin.ext
    rw [ePG_true_val]
    simp
  rw [h2] at h1
  exact h1

theorem fibre_isLocallyConstant_hasCompactSupport (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) ∧
      HasCompactSupport (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) := by
  refine ⟨isLocallyConstant_translate (HPG k (i + 1) (t + 1)) (sigX τ σ) f.1 (dEmb k i t) (continuous_dEmb i t)
    (dEmb_zero i t) (dEmb_add i t) y, ?_⟩
  obtain ⟨C, hC, hf⟩ := f.2
  let φ : Mir k ((i + 1) + t + 1) → Fin (t + 1) → k := fun c b =>
    -(((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _)
  have hφ : Continuous φ := by
    refine continuous_pi fun b => Continuous.neg ?_
    have h1 : Continuous fun c : Mir k ((i + 1) + t + 1) =>
        (((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
          Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_const.mul continuous_inv))
    exact (continuous_apply_apply _ _).comp h1
  refine HasCompactSupport.intro (hC.image hφ) fun x hx => ?_
  by_contra hne
  obtain ⟨h, hh, c, hc, e⟩ := hf (dEmb k i t x * y) hne
  refine hx ⟨c, hc, ?_⟩
  have e1 : h = dEmb k i t x * (y * c⁻¹) := by
    rw [← mul_assoc]
    exact eq_mul_inv_of_mul_eq e.symm
  funext b
  have h0 := hpg_entry_eq_zero i t h hh b
  rw [e1, dEmb_mul_entry] at h0
  exact neg_eq_of_add_eq_zero_right h0

end GlobalTheory.CompanionTheory.BZPhiPG.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateUnramifiedDegreeOne
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem lt_local_artin_inertia : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {Ωv : Type} [Field Ωv] [ValuativeRel Ωv] [TopologicalSpace Ωv] [IsValuativeTopology Ωv]
    [Algebra F Ωv] [ValuativeExtension F Ωv] [IsSepClosure F Ωv] [IsSepClosed Ωv]
    {π : 𝒪[F]} (hπ : Irreducible π) {f : PowerSeries 𝒪[F]} (hf : IsLubinTateSeries π f)
    (u : 𝒪[F]ˣ) (τ : Ωv ≃ₐ[F] Ωv), unramifiedDegree F Ωv τ = 1 →
    (∀ n, ∀ x ∈ lubinTateTorsion Ωv (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = (u : 𝒪[F]) • x) →
    ∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension F Ωv),
    ((localArtinMap F Ωv (unitsIncl F u⁻¹) ⟨y, hy⟩ : maximalAbelianExtension F Ωv) : Ωv) = τ y := by
  intro F _ _ _ _ Ωv _ _ _ _ _ _ _ _ π hπ f hf u τ hτd hτ y hy
  obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
  obtain ⟨n, m, h⟩ := exists_le_lubinTateField_sup_unramifiedTower hπ hf L
  have hE := isUnramifiedSubextension_unramifiedTower (K := F) (Ω := Ωv) m
  have := hE.1
  have := hE.isGalois
  have hab := isAbelianGalois_lubinTateField_sup hπ hf n.succ_pos hE
  have key := restrictAb_localArtinMap_lubinTate hπ hf n.succ_pos (unramifiedTower F Ωv m)
    hE.le_maximalUnramifiedExtension u⁻¹ 0 τ (by rw [hτd]; simp)
    (by intro x hx; rw [inv_inv]; exact hτ _ x hx)
  have hx : unitUniformizerPow hπ u⁻¹ 0 = unitsIncl F u⁻¹ := by
    rw [unitUniformizerPow_eq, zpow_zero, one_mul]
  rw [hx] at key
  have h2 := congrArg (fun σ => ((σ ⟨y, h hyL⟩ : (lubinTateField Ωv hπ hf (n + 1) ⊔ unramifiedTower F Ωv m : IntermediateField F Ωv)) : Ωv)) key
  simp only [restrictAb_apply, AlgEquiv.restrictNormalHom_apply] at h2
  exact h2

end GlobalTheory.CompanionTheory.LTLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapSingleAtEmb
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL PositivityTheory.Rg.Cz
open scoped Classical

namespace GlobalTheory.CompanionTheory.FrameCasimir

theorem sum_embeddings {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : Type} [AddCommMonoid N]
    (f : (E →+* ℂ) → N) :
    ∑ τ, f τ = ∑ v : InfinitePlace E, (f v.embedding + f (ComplexEmbedding.conjugate v.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : E →+* ℂ => InfinitePlace.mk τ) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hne : v.embedding ≠ ComplexEmbedding.conjugate v.embedding := by
    intro h
    have hc : v.IsComplex := IsTotallyComplex.isComplex v
    exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        exact (star_star τ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne]

theorem atEmb_embedding {E : Type} [Field E] (v : InfinitePlace E) (z : ℂ) :
    atEmb v.embedding z = (Pi.single v z : Cinf E) := by
  unfold atEmb
  rw [if_pos (by rw [InfinitePlace.mk_embedding])]
  congr 1 <;> simp

theorem map_single_atEmb {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {N : Type} [AddCommGroup N]
    [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (φ : Lie E a →ₗ[ℝ] N) (τ : E →+* ℂ) (i j : Fin a) (z : ℂ) :
    φ (toL (Matrix.single i j (atEmb τ z))) =
      z • cx τ φ i j + starRingEnd ℂ z • cx (ComplexEmbedding.conjugate τ) φ i j := by
  let L : Cinf E →ₗ[ℝ] N :=
    { toFun := fun x => φ (toL (Matrix.single i j x))
      map_add' := fun x y => by
        rw [Matrix.single_add]
        exact φ.map_add _ _
      map_smul' := fun r x => by
        rw [← Matrix.smul_single]
        exact φ.map_smul r _ }
  have hL : ∀ x, φ (toL (Matrix.single i j x)) = L x := fun _ => rfl
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [hL, atEmb_eq, map_add, map_smul, map_smul]
  simp only [cx, hL, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  have h1 := Complex.add_conj z
  have h2 := Complex.sub_conj z
  push_cast at h1 h2
  match_scalars
  · simp only [Complex.coe_algebraMap]; linear_combination (-1 / 2 : ℂ) * h1
  · simp only [Complex.coe_algebraMap]; linear_combination (Complex.I / 2 : ℂ) * h2 + z.im * Complex.I_mul_I

theorem alg_sq {R : Type} [Ring R] [Algebra ℂ R] (u w : R) :
    (u + w) * (u + w) - (Complex.I • u - Complex.I • w) * (Complex.I • u - Complex.I • w) =
      (2 : ℂ) • (u * u) + (2 : ℂ) • (w * w) := by
  rw [← smul_sub, smul_mul_smul_comm, Complex.I_mul_I]
  simp only [mul_add, add_mul, sub_mul, mul_sub]
  module

theorem alg_sum {R : Type} [Ring R] [Algebra ℂ R] {a : ℕ} (P : Fin a → Fin a → R) (c d : ℂ)
    (h0 : c * c + d * d = 0) (h1 : 2 * (c * d) = 1) :
    ∑ i, ∑ j, (c • P i j + d • P j i) * (c • P i j + d • P j i) = ∑ i, ∑ j, P i j * P j i := by
  have e : ∀ i j, (c • P i j + d • P j i) * (c • P i j + d • P j i) =
      (c * c) • (P i j * P i j) + (c * d) • (P i j * P j i) + (c * d) • (P j i * P i j) + (d * d) • (P j i * P j i) := by
    intro i j
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    module
  simp only [e, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun i j => P j i * P i j), Finset.sum_comm (f := fun i j => P j i * P j i)]
  generalize (∑ i, ∑ j, P i j * P i j) = S
  generalize (∑ i, ∑ j, P i j * P j i) = T
  calc (c * c) • S + (c * d) • T + (c * d) • T + (d * d) • S = (c * c + d * d) • S + (2 * (c * d)) • T := by module
    _ = T := by rw [h0, h1, zero_smul, one_smul, zero_add]

theorem iM_single {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) (z : ℂ) :
    iM (Matrix.single i j (Pi.single v z : Cinf E)) = Matrix.single i j (Pi.single v (Complex.I * z) : Cinf E) := by
  unfold iM
  rw [Matrix.smul_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp
  · simp [Pi.single_eq_of_ne hw]

theorem fr_val {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) :
    (fr (v, i, j) : Herm E a).1 = Matrix.single i j (Pi.single v ((1 + Complex.I) / 2) : Cinf E) +
      Matrix.single j i (Pi.single v (starRingEnd ℂ ((1 + Complex.I) / 2)) : Cinf E) := by
  change frU (v, i, j) + star (frU (v, i, j)) = _
  congr 1
  unfold frU
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp only [Pi.star_apply, Pi.single_eq_same, Complex.star_def]
  · simp [Pi.single_eq_of_ne hw]

theorem frameCas : FrameCas := by
  intro E _ _ _ a M _ _ _ _ φ
  set c : ℂ := (1 + Complex.I) / 2 with hc
  have hc0 : c * c + starRingEnd ℂ c * starRingEnd ℂ c = 0 := by
    simp only [hc, map_div₀, map_add, map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
  have hc1 : 2 * (c * starRingEnd ℂ c) = 1 := by
    simp only [hc, map_div₀, map_add, map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
    norm_num
  let P : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx v.embedding φ
  let Q : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx (ComplexEmbedding.conjugate v.embedding) φ
  let u : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => c • P v i j + starRingEnd ℂ c • P v j i
  let w : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => starRingEnd ℂ c • Q v i j + c • Q v j i
  have hs : ∀ v i j z, φ (toL (Matrix.single i j (Pi.single v z : Cinf E))) = z • P v i j + starRingEnd ℂ z • Q v i j := by
    intro v i j z
    rw [← atEmb_embedding]
    exact map_single_atEmb φ v.embedding i j z
  have hadd : ∀ A B : Matrix (Fin a) (Fin a) (Cinf E), φ (toL (A + B)) = φ (toL A) + φ (toL B) :=
    fun A B => φ.map_add (toL A) (toL B)
  have hfr : ∀ v i j, φ (toL (fr (v, i, j) : Herm E a).1) = u v i j + w v i j := by
    intro v i j
    rw [fr_val, hadd, hs, hs, Complex.conj_conj]
    simp only [u, w]
    abel
  have hiM : ∀ v i j, φ (toL (iM (fr (v, i, j) : Herm E a).1)) = Complex.I • u v i j - Complex.I • w v i j := by
    intro v i j
    have e : iM ((fr (v, i, j) : Herm E a).1) = iM (Matrix.single i j (Pi.single v c : Cinf E)) +
        iM (Matrix.single j i (Pi.single v (starRingEnd ℂ c) : Cinf E)) := by
      rw [fr_val]
      exact smul_add _ _ _
    rw [e, iM_single, iM_single, hadd, hs, hs]
    simp only [u, w, map_mul, Complex.conj_I, Complex.conj_conj]
    module
  have L1 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (fr k : Herm E a).1) * φ (toL (fr k : Herm E a).1) =
      ∑ v, ∑ i, ∑ j, (u v i j + w v i j) * (u v i j + w v i j) := by
    simp only [Fintype.sum_prod_type, hfr]
  have L2 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (iM (fr k : Herm E a).1)) * φ (toL (iM (fr k : Herm E a).1)) =
      ∑ v, ∑ i, ∑ j, (Complex.I • u v i j - Complex.I • w v i j) * (Complex.I • u v i j - Complex.I • w v i j) := by
    simp only [Fintype.sum_prod_type, hiM]
  rw [L1, L2, sum_embeddings, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hu : ∑ i, ∑ j, u v i j * u v i j = ∑ i, ∑ j, P v i j * P v j i :=
    alg_sum (P v) c (starRingEnd ℂ c) hc0 hc1
  have hw : ∑ i, ∑ j, w v i j * w v i j = ∑ i, ∑ j, Q v i j * Q v j i :=
    alg_sum (Q v) (starRingEnd ℂ c) c (by rw [add_comm]; exact hc0) (by rw [mul_comm (starRingEnd ℂ c)]; exact hc1)
  change _ = (2 : ℂ) • (∑ i, ∑ j, P v i j * P v j i + ∑ i, ∑ j, Q v i j * Q v j i)
  rw [← hu, ← hw, smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => alg_sq _ _

end GlobalTheory.CompanionTheory.FrameCasimir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicIffMemEmbedded
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaMem

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iotaM_castSucc_castSucc (n : ℕ) (y : Mir k n) (r c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) =
      ((y : GL (Fin (n + 1)) k) : Matrix _ _ k) r c := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

theorem iotaM_last_castSucc (n : ℕ) (y : Mir k n) (c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.last (n + 1)) (Fin.castSucc c) = 0 := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

end GlobalTheory.CompanionTheory.LeibPhi.IotaMem

namespace GlobalTheory.CompanionTheory.LeibPhi

open GlobalTheory.CompanionTheory.LeibPhi.IotaMem in

theorem mem_mirabolicParabolic_iff_iotaM_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)) :
    y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff, mem_mirabolicParabolic_iff]
  have eF : ∀ a : Fin m, eGP m (j + 1) ⟨false, a⟩ = Fin.castSucc (eGP m j ⟨false, a⟩) := by
    intro a
    ext
    simp [blockIndex_false_val]
  have eT : ∀ b : Fin (j + 1),
      eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = Fin.castSucc (eGP m j ⟨true, b⟩) := by
    intro b
    ext
    simp [blockIndex_true_val]
  have eL : eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = Fin.last (m + j + 1) := by
    ext
    simp [blockIndex_true_val]
    omega
  constructor
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      rw [eL, eF]
      exact iotaM_last_castSucc k (m + j) y _
    | cast b =>
      rw [eT, eF]
      rw [iotaM_castSucc_castSucc k (m + j) y]
      exact h b a
  · intro h b a
    have hb := h (Fin.castSucc b) a
    rw [eT, eF, iotaM_castSucc_castSucc k (m + j) y] at hb
    exact hb

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentLeParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem one_add_colMat_apply_eq_zero_of_ne_last (k : Type) [Field k] (n : ℕ) (v : Fin n → k)
    {r c : Fin (n + 1)} (hc : c ≠ Fin.last n) (hrc : r ≠ c) :
    (1 + GlobalTheory.BZMir.colMat k n v) r c = 0 := by
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat, if_neg hc, if_neg hrc,
    add_zero]

theorem mirUin_le_HGP (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) : MirUin k (m + j) ≤ MirabolicParabolic k m j := by
  intro g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  rw [GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff]
  intro b a
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  rw [hmat]
  have ha := a.isLt
  apply one_add_colMat_apply_eq_zero_of_ne_last
  · intro h
    have h' := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val, Fin.val_last] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val] at h'
    omega

end GlobalTheory.CompanionTheory.LeibPhi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusMirabolicBlockFactor
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : ℝ) (h : MirabolicParabolic k (i + 1) t), dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) = dpow (i + 1) s (gpProj k (i + 1) t h).1 * dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := by
  intro k _ _ _ _ i t s h
  have key : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (Matrix.GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  have hdet : Matrix.GeneralLinearGroup.det
      ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) =
      Matrix.GeneralLinearGroup.det (GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 *
        Matrix.GeneralLinearGroup.det
          (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).2 : GlobalTheory.BZMir.Mir k t) :
            GL (Fin (t + 1)) k) := by
    have hp := GlobalTheory.SmGL.det_parab k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
      (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h)
    rw [Fintype.prod_bool] at hp
    exact hp.trans (mul_comm _ _)
  rw [show GlobalTheory.RgGu.Leib.dpowM ((i + 1) + t) s (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) =
      GlobalTheory.BZMir.Leib.dpow ((i + 1) + t + 1) s
        ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) from rfl,
    key, key, key, hdet, map_mul]

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

