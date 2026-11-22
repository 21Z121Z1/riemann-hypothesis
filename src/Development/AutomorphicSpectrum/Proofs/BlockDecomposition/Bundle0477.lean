import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeFlagTransitiveLocal
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.Iwasawa

section Abstract

variable {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R)

theorem isEvenInt_map {V : Type} [AddCommGroup V] [Module R V] {h : V → V → R} (e : V ≃ₗ[R] V)
    (he : ∀ x y, h (e x) (e y) = h x y) {L : Submodule 𝔬 V} (hL : IsEvenInt c 𝔬 h L) :
    IsEvenInt c 𝔬 h (L.map (e.toLinearMap.restrictScalars 𝔬)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change h (e x) (e y) ∈ 𝔬
    rw [he]
    exact hL.1 x hx y hy
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, e'⟩ := hL.2 x hx
    refine ⟨a, ha, ?_⟩
    change h (e x) (e x) = _
    rw [he, e']

theorem isMaxEven_map {V : Type} [AddCommGroup V] [Module R V] {h : V → V → R} (e : V ≃ₗ[R] V)
    (he : ∀ x y, h (e x) (e y) = h x y) {L : Submodule 𝔬 V} (hL : IsMaxEven c 𝔬 h L) :
    IsMaxEven c 𝔬 h (L.map (e.toLinearMap.restrictScalars 𝔬)) := by
  obtain ⟨⟨hfg, hsp⟩, hev, hmax⟩ := hL
  refine ⟨⟨hfg.map _, ?_⟩, isEvenInt_map c 𝔬 e he hev, fun L' hL' hle => ?_⟩
  · have h1 : ((L.map (e.toLinearMap.restrictScalars 𝔬) : Submodule 𝔬 V) : Set V) =
        e.toLinearMap '' (L : Set V) := by
      ext z
      rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top]
    exact e.surjective
  · have hs : ∀ x y, h (e.symm x) (e.symm y) = h x y := fun x y => by
      rw [← he (e.symm x), e.apply_symm_apply, e.apply_symm_apply]
    have h1 := isEvenInt_map c 𝔬 e.symm hs hL'
    have h2 : L ≤ L'.map (e.symm.toLinearMap.restrictScalars 𝔬) := fun y hy =>
      ⟨e y, hle ⟨y, hy, rfl⟩, by simp⟩
    intro z hz
    exact ⟨e.symm z, hmax _ h1 h2 ⟨z, hz, rfl⟩, by simp⟩

variable {n r : ℕ}

theorem hform_eq (Jm : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform c Jm x y = (fun i => c (x i)) ⬝ᵥ (Jm *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cT_mul_apply (Jm : Matrix (Fin n) (Fin n) R) {k l : ℕ} (M : Matrix (Fin n) (Fin k) R)
    (N : Matrix (Fin n) (Fin l) R) (i : Fin k) (j : Fin l) :
    (cT c M * Jm * N) i j = Formalism.UG.hform c Jm (fun a => M a i) (fun a => N a j) := by
  simp only [Matrix.mul_apply, cT, Formalism.UG.hform, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem isHerm_hform (hc : ∀ a, c (c a) = a) (Jm : Matrix (Fin n) (Fin n) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) : IsHerm c (Formalism.UG.hform c Jm) where
  add_right x y z := by
    simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right a x y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  symm x y := by
    simp only [Formalism.UG.hform, map_sum, map_mul, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ]
    ring

theorem isPerfect_hform (hc : ∀ a, c (c a) = a) (Jm : Matrix (Fin n) (Fin n) R)
    (hd : IsUnit Jm.det) : IsPerfect (Formalism.UG.hform c Jm) where
  nondeg x hx := by
    have h1 : (fun i => c (x i)) ᵥ* Jm = 0 := by
      funext j
      have h2 := hx (Pi.single j 1)
      rw [hform_eq, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h2
      exact h2
    have h2 : (fun i => c (x i)) = 0 := by
      have h3 := congrArg (fun w => w ᵥ* Jm⁻¹) h1
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hd] using h3
    funext i
    have h3 := congrFun h2 i
    have h4 : c (x i) = 0 := h3
    rw [← hc (x i), h4, map_zero]
    rfl
  repr f := by
    let w : Fin n → R := fun j => f (fun k => if j = k then 1 else 0)
    let u : Fin n → R := w ᵥ* Jm⁻¹
    refine ⟨fun i => c (u i), fun y => ?_⟩
    rw [hform_eq]
    have h1 : (fun i => c (c (u i))) = u := funext fun i => hc _
    rw [h1, Matrix.dotProduct_mulVec]
    have h2 : u ᵥ* Jm = w := by
      simp only [u, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hd, Matrix.vecMul_one]
    rw [h2, LinearMap.pi_apply_eq_sum_univ f y]
    simp only [dotProduct, smul_eq_mul, w]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hform_mulVec (Jm g : Matrix (Fin n) (Fin n) R) (hg : cT c g * Jm * g = Jm) (x y : Fin n → R) :
    Formalism.UG.hform c Jm (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform c Jm x y := by
  have h1 : (fun i => c ((g *ᵥ x) i)) = (fun i => c (x i)) ᵥ* cT c g := by
    funext i
    simp only [mulVec, vecMul, dotProduct, cT, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hform_eq, hform_eq, h1, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hg]

theorem exists_mat (Jm : Matrix (Fin n) (Fin n) R) (p : (Fin n → R) ≃ₗ[R] (Fin n → R))
    (hp : ∀ x y, Formalism.UG.hform c Jm (p x) (p y) = Formalism.UG.hform c Jm x y) :
    ∃ P : GL (Fin n) R, P ∈ Formalism.UG.UJ c Jm ∧ ∀ y, (P : Matrix (Fin n) (Fin n) R) *ᵥ y = p y := by
  let P : GL (Fin n) R := ⟨LinearMap.toMatrix' p.toLinearMap, LinearMap.toMatrix' p.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨P, ?_, fun y => LinearMap.toMatrix'_mulVec _ _⟩
  change cT c (LinearMap.toMatrix' p.toLinearMap) * Jm * LinearMap.toMatrix' p.toLinearMap = Jm
  ext i j
  rw [cT_mul_apply]
  simp only [LinearMap.toMatrix'_apply]
  have h1 := hp (Pi.single i 1) (Pi.single j 1)
  refine h1.trans ?_
  simp [Formalism.UG.hform, Pi.single_apply]

theorem exists_coeff {V : Type} [AddCommGroup V] [Module R V] (x : Fin r → V) (j : Fin r) {w : V}
    (hw : w ∈ Submodule.span R (x '' {i | i ≤ j})) :
    ∃ b : Fin r → R, (∀ i, j < i → b i = 0) ∧ w = ∑ i, b i • x i := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, hi, rfl⟩ := hw
    refine ⟨Pi.single i 1, fun k hk => ?_, ?_⟩
    · exact Pi.single_eq_of_ne (ne_of_gt (lt_of_le_of_lt hi hk)) _
    · simp [Pi.single_apply]
  | zero => exact ⟨0, by simp, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨b₁, h₁, rfl⟩ := ha
    obtain ⟨b₂, h₂, rfl⟩ := hb
    refine ⟨b₁ + b₂, fun i hi => by simp [h₁ i hi, h₂ i hi], ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | smul t a _ ha =>
    obtain ⟨b, hb, rfl⟩ := ha
    refine ⟨t • b, fun i hi => by simp [hb i hi], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem cT_mul_map {A B : Type} [CommRing A] [CommRing B] (s : A →+* A) (c : B →+* B) (f : A →+* B)
    (h : ∀ t, c (f t) = f (s t)) {k l : ℕ} (M : Matrix (Fin n) (Fin k) A) (Jm : Matrix (Fin n) (Fin n) A)
    (N : Matrix (Fin n) (Fin l) A) :
    cT c (M.map f) * Jm.map f * N.map f = (cT s M * Jm * N).map f := by
  have h1 : cT c (M.map f) = (cT s M).map f := by
    ext i j
    simp [cT, h]
  rw [h1, Matrix.map_mul, Matrix.map_mul]

theorem iwasawa_abs (hc : ∀ a, c (c a) = a) (Jm : Matrix (Fin n) (Fin n) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (hd : IsUnit Jm.det) (Xm Ym : Matrix (Fin n) (Fin r) R)
    (hxx : cT c Xm * Jm * Xm = 0) (hyy : cT c Ym * Jm * Ym = 0) (hxy : cT c Xm * Jm * Ym = 1)
    (hFT : FlagTransitive c 𝔬) (Λ : Submodule 𝔬 (Fin n → R))
    (hΛ : IsMaxEven c 𝔬 (Formalism.UG.hform c Jm) Λ) (g : GL (Fin n) R) (hg : g ∈ Formalism.UG.UJ c Jm) :
    ∃ P : GL (Fin n) R, P ∈ Formalism.UG.UJ c Jm ∧
      (∀ y, y ∈ Λ ↔ ((P⁻¹ * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ y ∈ Λ) ∧
      ∃ B : Matrix (Fin r) (Fin r) R, B.BlockTriangular id ∧
        (P : Matrix (Fin n) (Fin n) R) * Xm = Xm * B := by
  have hgm : cT c (g : Matrix (Fin n) (Fin n) R) * Jm * (g : Matrix (Fin n) (Fin n) R) = Jm := hg
  let e : (Fin n → R) ≃ₗ[R] (Fin n → R) := Matrix.toLinearEquiv' (g : Matrix (Fin n) (Fin n) R)
    ⟨((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R), by simp, by simp⟩
  have heIso : ∀ a b, Formalism.UG.hform c Jm (e a) (e b) = Formalism.UG.hform c Jm a b := fun a b =>
    hform_mulVec c Jm _ hgm a b
  let x : Fin r → Fin n → R := fun i a => Xm a i
  let y : Fin r → Fin n → R := fun i a => Ym a i
  have hFr : IsFrame (Formalism.UG.hform c Jm) x y :=
    ⟨fun i j => by rw [← cT_mul_apply, hxx]; rfl, fun i j => by rw [← cT_mul_apply, hyy]; rfl,
      fun i j => by rw [← cT_mul_apply, hxy, Matrix.one_apply]⟩
  obtain ⟨p, ⟨hpi, hpL⟩, hpf⟩ := hFT _ (Formalism.UG.hform c Jm) (isHerm_hform c hc Jm hJ)
    (isPerfect_hform c hc Jm hd) r x y hFr Λ (Λ.map (e.toLinearMap.restrictScalars 𝔬)) hΛ
    (isMaxEven_map c 𝔬 e heIso hΛ)
  obtain ⟨P, hP, hPy⟩ := exists_mat c Jm p hpi
  refine ⟨P, hP, fun w => ?_, ?_⟩
  · have hz : p (((P⁻¹ * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w) = e w := by
      rw [← hPy, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
      rfl
    rw [hpL (((P⁻¹ * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w), hz]
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w', hw', h'⟩
      have h2 : w' = w := e.injective h'
      exact h2 ▸ hw'
  · choose b hb0 hb using fun j => exists_coeff x j (hpf j)
    refine ⟨Matrix.of fun i j => b j i, fun i j hij => hb0 j i hij, ?_⟩
    ext a j
    have h1 := congrFun (hb j) a
    rw [← hPy] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mul_apply, Matrix.of_apply]
    refine h1.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)

end Abstract

section Place

theorem sigR_sigR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (K : Type) [CommRing K] [Algebra F K] (t : K ⊗[F] E) :
    sigR K σ (sigR K σ t) = t := by
  have hs : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hs]
  | add a b ha hb => simp only [map_add, ha, hb]

end Place

theorem iwasawa_loc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)), FlagTransitive (sigR (Fv F v) σ) (intLoc F E v) → ∀ Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → ∀ g : GLoc σ J v, ∃ p : GLoc σ J v, ∃ k ∈ stabLat σ J Λ, g = p * k ∧ ∃ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id ∧ (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW v hFT Λ hΛ g
  have hs : ∀ t : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) t) = inclR (F := F) (Fv F v) (σ t) := by
    intro t
    simp [sigR, inclR]
  have hJm : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) J j i) = JR (Fv F v) J i j := by
    intro i j
    simp only [JR, Matrix.map_apply, hs, hJ.1]
  have hdet : IsUnit (JR (F := F) (Fv F v) J).det := by
    have h1 : (JR (F := F) (Fv F v) J).det = inclR (F := F) (Fv F v) J.det :=
      (RingHom.map_det _ _).symm
    rw [h1]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hg : matHom _ σ J g ∈ Formalism.UG.UJ (sigR (Fv F v) σ) (JR (Fv F v) J) := Subtype.property _
  obtain ⟨P, hP, hk, B, hB, hPB⟩ := iwasawa_abs (sigR (Fv F v) σ) (intLoc F E v) (sigR_sigR hCM (Fv F v))
    (JR (Fv F v) J) hJm hdet (X.map (inclR (F := F) (Fv F v))) (Y.map (inclR (F := F) (Fv F v)))
    ((cT_mul_map (σ : E →+* E) (sigR (Fv F v) σ) (inclR (F := F) (Fv F v)) hs X J X).trans (by rw [hW.xx]; simp))
    ((cT_mul_map (σ : E →+* E) (sigR (Fv F v) σ) (inclR (F := F) (Fv F v)) hs Y J Y).trans (by rw [hW.yy]; simp))
    ((cT_mul_map (σ : E →+* E) (sigR (Fv F v) σ) (inclR (F := F) (Fv F v)) hs X J Y).trans (by rw [hW.xy]; simp))
    hFT Λ hΛ _ hg
  let p : GLoc σ J v := (⟨P, hP⟩ : HR (Fv F v) σ J)
  have hp : matHom _ σ J p = P := rfl
  refine ⟨p, p⁻¹ * g, ?_, (mul_inv_cancel_left p g).symm, B, hB, hPB⟩
  rw [mem_stabLat]
  intro w
  rw [map_mul, map_inv, hp]
  exact hk w

end GlobalTheory.CompanionTheory.KFin.Iwasawa

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSubmoduleOfBumps
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem mem_of_bumps {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (y : cIndSpace H ρ) (hy : ∀ g, ∀ x ∈ K, y.1.1.1 (g * x) = y.1.1.1 g)
    (S : Submodule ℂ (cIndSpace H ρ)) (hS : ∀ c B, IsBump H ρ K c (y.1.1.1 c) B → B ∈ S) : y ∈ S := by
  classical
  obtain ⟨C, hC, hsupp⟩ := y.2
  have hyeq : ∀ (a : H) (g : G), y.1.1.1 ((a : G) * g) = ρ a (y.1.1.1 g) := y.1.1.2
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K : Set G)) (fun c _ => by
    have : (fun y => c⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 c :=
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
    filter_upwards [this] with y hy
    exact ⟨c⁻¹ * y, hy, by group⟩)
  let T : Finset (DoubleCoset.Quotient (H : Set G) (K : Set G)) := t.image (DoubleCoset.mk H K)
  have hres := fun d : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H ρ (GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H K hKo (Quotient.out d)) y
  choose f hf1 hf0 using hres
  have hbump : ∀ d, IsBump H ρ K (Quotient.out d) (y.1.1.1 (Quotient.out d)) (f d) := by
    intro d
    refine ⟨fun a x hx => ?_, fun g hg => hf0 d g ?_⟩
    · rw [hf1 d _ ⟨a, a.2, x, hx, rfl⟩, hy _ x hx, hyeq]
    · rintro ⟨a, ha, x, hx, e⟩
      exact hg ⟨⟨a, ha⟩, x, hx, e⟩
  have hoff : ∀ (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) (g : G), DoubleCoset.mk H K g ≠ d →
      (f d).1.1.1 g = 0 := by
    intro d g hne
    apply hf0
    rintro ⟨a, ha, x, hx, e⟩
    apply hne
    rw [← DoubleCoset.out_eq' H K d]
    exact ((DoubleCoset.eq H K _ _).2 ⟨a, ha, x, hx, e⟩).symm
  have hmem : ∑ d ∈ T, f d ∈ S := S.sum_mem fun d _ => hS _ _ (hbump d)
  have hval : ∀ g, y.1.1.1 g = (∑ d ∈ T, f d).1.1.1 g := by
    intro g
    let ev : cIndSpace H ρ →ₗ[ℂ] W :=
      (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype
    have hsum : (∑ d ∈ T, f d).1.1.1 g = ∑ d ∈ T, (f d).1.1.1 g := map_sum ev _ _
    rw [hsum]
    by_cases hg : DoubleCoset.mk H K g ∈ T
    · rw [Finset.sum_eq_single_of_mem _ hg (fun d _ hd => hoff d g (Ne.symm hd))]
      obtain ⟨a, ha, x, hx, e⟩ := (DoubleCoset.eq H K _ _).1 (DoubleCoset.out_eq' H K (DoubleCoset.mk H K g))
      exact (hf1 _ g ⟨a, ha, x, hx, e⟩).symm
    · rw [Finset.sum_eq_zero (fun d hd => hoff d g (fun h => hg (h ▸ hd)))]
      by_contra hne
      obtain ⟨a, ha, c', hc', e⟩ := hsupp g hne
      obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
      obtain ⟨x, hx, rfl⟩ := hcc
      apply hg
      have : DoubleCoset.mk H K c = DoubleCoset.mk H K g :=
        (DoubleCoset.eq H K _ _).2 ⟨a, ha, x, hx, by rw [e]; group⟩
      rw [← this]
      exact Finset.mem_image_of_mem _ hc
  have e : y = ∑ d ∈ T, f d := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hval g
  rw [e]
  exact hmem

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureDataStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_cell_structure_data : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ),
  (MirUin k ((i + 1) + t + 1)).Normal ∧ IsOpen ((mirChar k ψ ((i + 1) + t)).ker : Set (MirUin k ((i + 1) + t + 1))) ∧
    IsClosed (Cl k i t) ∧ (∀ h ∈ HPG k (i + 1) (t + 1), ∀ x ∈ Cl k i t, h * x ∈ Cl k i t) ∧
    (∀ x ∈ Cl k i t, ∀ u ∈ MirUin k ((i + 1) + t + 1), x * u ∈ Cl k i t) ∧
    ∀ L₁ L₂ : Subgroup (Mir k ((i + 1) + t + 1)), L₁ ≤ MirUin k ((i + 1) + t + 1) → L₂ ≤ MirUin k ((i + 1) + t + 1) →
      IsCompact (L₁ : Set (Mir k ((i + 1) + t + 1))) → IsCompact (L₂ : Set (Mir k ((i + 1) + t + 1))) →
      ∃ L : Subgroup (Mir k ((i + 1) + t + 1)), L ≤ MirUin k ((i + 1) + t + 1) ∧ IsCompact (L : Set (Mir k ((i + 1) + t + 1))) ∧
        L₁ ≤ L ∧ L₂ ≤ L := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Grp.main | exact GlobalTheory.CompanionTheory.BZPhiPG.Grp.main | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCompactModParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Coc

theorem continuous_levi_mir (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : Continuous (levi k n) := by
  have hval : Continuous fun g : GL (Fin n) k => GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k) :=
    GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp n Units.continuous_val
  have hinv : Continuous fun g : GL (Fin n) k =>
      GlobalTheory.BZMir.glEmbMat k n ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp n Units.continuous_coe_inv
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact hval
  · exact hinv

theorem hgp_cocompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ C : Set (Mir k ((i + 1) + t)), IsCompact C ∧
      ∀ g : Mir k ((i + 1) + t), ∃ h ∈ MirabolicParabolic k (i + 1) t, ∃ c ∈ C, g = h * c := by
  intro k _ _ _ _ i t
  refine ⟨GlobalTheory.BZMir.levi k ((i + 1) + t) ''
      (GlobalTheory.SplitWeil.KO k (Fin ((i + 1) + t)) : Set (GL (Fin ((i + 1) + t)) k)),
    GlobalTheory.SplitFlip.isCompact_KO.image (GlobalTheory.CompanionTheory.BZPhiPG.Coc.continuous_levi_mir k _), ?_⟩
  intro g
  obtain ⟨p, w, hw, hx⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : (i + 1) + t = (i + 1) + t)))
    (GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t) g)
  refine ⟨g * (GlobalTheory.BZMir.levi k _ w)⁻¹, ?_, GlobalTheory.BZMir.levi k _ w, ⟨w, hw, rfl⟩,
    (inv_mul_cancel_right g _).symm⟩
  rw [GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic]
  have hproj : GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t) (g * (GlobalTheory.BZMir.levi k _ w)⁻¹) = p := by
    rw [map_mul, map_inv, GlobalTheory.CompanionTheory.MirLevi.mirProj_levi, hx, mul_inv_cancel_right]
  rw [hproj]
  exact p.2

end GlobalTheory.CompanionTheory.BZPhiPG.Coc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_double_coset_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ),
  (∀ p ∈ Cl k i t, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)),
      p = h * dEmb k i t d * sEmb k ((i + 1) + t) m) ∧
  (∀ p, p ∉ Cl k i t → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)),
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells | exact GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharactersProductOneStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_characters_product_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ) *
    (((dpowM i (1 / 2) (pgProj k i (t + 1) h).1 : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel | exact GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusMirabolicBlockFactorStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_mirabolic_block_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : ℝ) (h : MirabolicParabolic k (i + 1) t), dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) = dpow (i + 1) s (gpProj k (i + 1) t h).1 * dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp | exact GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusParabolicProjFactorStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_parabolic_proj_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp | exact GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnCompactParabolicStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_trivial_on_compact_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ) (e : Fin a ⊕ Fin b ≃ Fin n) (K : Subgroup (GL (Fin n) k)), IsCompact (K : Set (GL (Fin n) k)) → ∀ p : parab k (two e), (p : GL (Fin n) k) ∈ K → deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact | exact GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulVec_mid_block_decomp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t) (v : Fin t → k), ∃ x : Fin i → k, ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) = topV k i t x + midV k i t ((((qBlocks k i t q).2 : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top | exact GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.N2TopRealStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.n2_top_real : PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter := by
  first | exact @GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | exact GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | (intros; apply GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitPreimageEq
section
open Matrix
open PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.EllProp

theorem twConj_twConj {G : Type*} [Group G] (θ : Monoid.End G) (x g d : G) :
    twConj θ x (twConj θ g d) = twConj θ (g * x) d := by
  simp only [twConj, map_mul]
  group

theorem orbit_preimage_eq {G : Type*} [Group G] (θ : Monoid.End G) (g d : G) (C : Set G) :
    {x | twConj θ x (twConj θ g d) ∈ C} = (fun y => g⁻¹ * y) '' {y | twConj θ y d ∈ C} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, twConj_twConj]
  constructor
  · intro h
    exact ⟨g * x, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem ellProperOf : EllProperOf := by
  intro hD hP _ n d hd C hC
  obtain ⟨g, d', z, h1, h2, h3, rfl⟩ := hD n d hd
  rw [orbit_preimage_eq]
  exact (hP n d' z h1 h2 h3 C hC).image (continuous_const.mul continuous_id)

end GlobalTheory.CompanionTheory.EllProp
end

