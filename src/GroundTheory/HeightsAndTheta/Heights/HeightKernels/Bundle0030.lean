import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0028

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeBasisExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix NumberField

noncomputable section

namespace DualLatticeBasisExistsAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem eq_zero_of_dotProduct_gens (F : HermLattice K i) (s : Finset (Fin i → K))
    (hs : Submodule.span (𝓞 K) (s : Set (Fin i → K)) = F.lattice) (φ : Fin i → K)
    (h : ∀ g ∈ s, φ ⬝ᵥ g = 0) : φ = 0 := by
  let L : (Fin i → K) →ₗ[K] K :=
    { toFun := fun x => φ ⬝ᵥ x
      map_add' := dotProduct_add φ
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have h1 : F.lattice ≤ (LinearMap.ker L).restrictScalars (𝓞 K) := by
    rw [← hs, Submodule.span_le]
    intro g hg
    exact h g hg
  have h2 : Submodule.span K (F.lattice : Set (Fin i → K)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    intro x hx
    exact h1 hx
  rw [F.span_eq, top_le_iff] at h2
  funext j
  have hj : Pi.single j (1 : K) ∈ LinearMap.ker L := by rw [h2]; trivial
  have : φ ⬝ᵥ Pi.single j (1 : K) = 0 := hj
  simpa [dotProduct_single] using this

theorem dualLattice_fg (F : HermLattice K i) : (dualLattice F).FG := by
  classical
  obtain ⟨s, hs⟩ := F.fg

  let G : (Fin i → K) →ₗ[ℤ] (s → K) :=
    { toFun := fun φ g => φ ⬝ᵥ (g : Fin i → K)
      map_add' := fun φ ψ => by funext g; simp [add_dotProduct]
      map_smul' := fun c φ => by
        funext g
        show (c • φ) ⬝ᵥ (g : Fin i → K) = c • (φ ⬝ᵥ (g : Fin i → K))
        exact smul_dotProduct c φ _ }
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    refine eq_zero_of_dotProduct_gens F s hs φ (fun g hg => ?_)
    exact congrFun hφ ⟨g, hg⟩

  let ι : (s → 𝓞 K) →ₗ[ℤ] (s → K) :=
    LinearMap.pi (fun g => ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ).comp (LinearMap.proj g))
  have hle : (dualLattice F).map G ≤ LinearMap.range ι := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hv : ∀ g : s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = φ ⬝ᵥ (g : Fin i → K) := fun g =>
      hφ g (hs ▸ Submodule.subset_span g.2)
    choose a ha using hv
    exact ⟨a, funext fun g => ha g⟩
  have hfg : ((dualLattice F).map G).FG := by
    have e : (dualLattice F).map G = (((dualLattice F).map G).comap ι).map ι := by
      rw [Submodule.map_comap_eq, inf_eq_right.mpr hle]
    rw [e]
    exact (IsNoetherian.noetherian _).map ι
  exact Submodule.fg_of_fg_map_injective G hG hfg

end DualLatticeBasisExistsAlt

open DualLatticeBasisExistsAlt in

theorem DualLatticeBasisExists.proof : DualLatticeBasisExists.Statement := by
  intro K _ _ i F
  classical
  have : Module.Finite ℤ (dualLattice F) := Module.Finite.iff_fg.mpr (dualLattice_fg F)
  exact ⟨Module.Free.ChooseBasisIndex ℤ (dualLattice F), inferInstance, inferInstance,
    ⟨Module.Free.chooseBasis ℤ (dualLattice F)⟩⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineConj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding

noncomputable section

namespace DualLineConjugation

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def conjPerm (K : Type) [Field K] : Equiv.Perm (K →+* ℂ) :=
  Function.Involutive.toPerm _ (involutive_conjugate K)

omit [Fintype T] [DecidableEq T] in

theorem conj_mulVec (b : Module.Basis T ℤ (dualLattice F)) (w : (K →+* ℂ) × Fin i → ℂ) :
    (fun t => starRingEnd ℂ ((dualEmbMatrix b *ᵥ w) t)) =
      dualEmbMatrix b *ᵥ fun p => starRingEnd ℂ (w (conjugate p.1, p.2)) := by
  funext t
  simp only [mulVec, dotProduct, map_sum, map_mul]
  refine Fintype.sum_equiv ((conjPerm K).prodCongr (Equiv.refl _)) _ _ fun p => ?_
  simp [conjPerm, dualEmbMatrix]

theorem recover_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualRecover b hb (fun t => starRingEnd ℂ (z t)) =
      fun p => starRingEnd ℂ (dualRecover b hb z (conjugate p.1, p.2)) := by
  have h1 : ∀ w, (dualRecover b hb).symm w = dualEmbMatrix b *ᵥ w := fun w => by
    simp [dualRecover]
  apply (dualRecover b hb).symm.injective
  rw [LinearEquiv.symm_apply_apply, h1, ← conj_mulVec b (dualRecover b hb z), ← h1,
    LinearEquiv.symm_apply_apply]

theorem re_conj_form {n : Type} [Fintype n] (H : Matrix n n ℂ) (v : n → ℂ) :
    (star (fun j => starRingEnd ℂ (v j)) ⬝ᵥ (H *ᵥ fun j => starRingEnd ℂ (v j))).re =
      (star v ⬝ᵥ (H.map (starRingEnd ℂ) *ᵥ v)).re := by
  rw [← Complex.conj_re (star v ⬝ᵥ _)]
  congr 1
  simp [dotProduct, mulVec, map_sum, map_mul]

theorem normSq_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualNormSq b hb (fun t => starRingEnd ℂ (z t)) = dualNormSq b hb z := by
  unfold dualNormSq
  rw [recover_conj]
  refine Fintype.sum_equiv (conjPerm K) _ _ fun σ => ?_
  have hσ : conjPerm K σ = conjugate σ := rfl
  rw [hσ, F.conj σ]
  exact re_conj_form (F.metric σ) fun j => dualRecover b hb z (conjugate σ, j)

end DualLineConjugation

theorem DualLineConj.proof : DualLineConj.Statement := by
  intro K _ _ i F T _ _ b hb z
  show Real.sqrt (dualNormSq b hb fun t => starRingEnd ℂ (z ⟨(), t⟩)) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  rw [DualLineConjugation.normSq_conj b hb fun t => z ⟨(), t⟩]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLineOfLargeDegreeDual
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem LineOfLargeDegreeFromZ.proofDual (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hArith : DualArithVar.Statement)
    (hSemi : DualLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : DualLineConj.Statement) (hPt : DualPointLineDegree.Statement)
    (hTop : DualTopBound.Statement) (hPos : DualGeomDegPos.Statement) :
    LineOfLargeDegreeFromZ.Statement := by
  intro hZ1 hZ2 hEx K _ _ i hi F ε hε
  obtain ⟨II, hII⟩ := hEx
  obtain ⟨T, _, _, ⟨b⟩⟩ := hBasis K i F
  have hb := hBij K i F T b
  set A := dualLine F b hb with hA
  set e : ℝ := -F.slope + 1 / 2 * Real.log i + ε with he
  by_contra hne
  push Not at hne
  have hW : ∀ W : Ideal (MRing (dualBlocks T)), IsArithVar W 1 → dualIdeal b ≤ W →
      e * degC W ≤ II Unit (dualBlocks T) W 1 ![A] := by
    intro W hW1 hPW
    obtain ⟨hdeg, K', iF, iN, iA, v, hv, hline⟩ := hPt K i F T b hb II hII W hW1 hPW
    have hlt := hne K' iF iN iA v hv
    rw [hline] at hlt
    have hd : (0 : ℝ) < degC W := by exact_mod_cast hdeg
    have h1 : e < II Unit (dualBlocks T) W 1 ![A] / degC W := by
      rw [neg_div] at hlt
      linarith
    exact ((lt_div_iff₀ hd).mp h1).le
  have hV : IsArithVar (dualIdeal b) (i - 1 + 1) := by
    rw [Nat.sub_add_cancel hi]; exact hArith K i F T b hi
  have hZ := hZ1 Unit (dualBlocks T) (dualIdeal b) ⊥ (i - 1) A e II hII hV
    bot_le (hSemi K i F T b hb) (hNef _ _ _ _ fun _ => zero_le_one) (hConj K i F T b hb) hW
  rw [Nat.sub_add_cancel hi] at hZ
  have hT := hTop hZ2 K i F T b hb II hi hII
  have hG := hPos K i F T b hb hi
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have key : (i : ℝ) * e * geomDeg (dualIdeal b) A (i - 1) ≤
      (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * geomDeg (dualIdeal b) A (i - 1) := hZ.trans hT
  have : (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) ≤ 0 := by
    rw [he] at key
    nlinarith
  have : 0 < (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) :=
    mul_pos (mul_pos hi' hε) hG
  linarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PProjPtsOfPlane
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace ProjectivePointsOfPlane

theorem map_eval₂_int {ι A B : Type*} [CommRing A] [CommRing B] (k : A →+* B) (c : ℤ →+* A) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (eval₂ c g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem map_aeval_int {ι A B : Type*} [CommRing A] {_ : Algebra ℤ A} [CommRing B] (k : A →+* B) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (aeval g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [aeval_def, map_eval₂_int]

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def formPoly (p : Σ _ : Unit, ProjIdx K i) : MvPolynomial (Fin i) K :=
  C (integralBasis K p.2.1) * X p.2.2

theorem eval₂_formPoly (σ : K →+* ℂ) (v : Fin i → ℂ) (p : Σ _ : Unit, ProjIdx K i) :
    eval₂Hom σ v (formPoly p) = projPlanePt σ v p := by
  simp [formPoly, projPlanePt]

end ProjectivePointsOfPlane

open ProjectivePointsOfPlane in

theorem ProjPtsOfPlane.proof : ProjPtsOfPlane.Statement := by
  intro K _ _ i σ v hv
  classical
  refine ⟨fun _ => ?_, fun f hf => ?_⟩
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    obtain ⟨m⟩ := (integralBasis K).index_nonempty
    refine ⟨(m, j), ?_⟩
    simp only [projPlanePt]
    exact mul_ne_zero ((map_ne_zero σ).mpr ((integralBasis K).ne_zero m)) hj
  · have h0 : mConeMap (projSpaceCoord K i) f = 0 := hf
    have h1 := congrArg (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) h0
    unfold mConeMap at h1
    rw [map_zero, map_aeval_int] at h1
    have hy : (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) ∘
        (fun p => C (projSpaceCoord K i p) * X p.1) =
        (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) ∘ formPoly := by
      funext p
      simp [projSpaceCoord, formPoly]
    rw [hy, ← map_eval₂_int (c := Int.castRingHom _)] at h1
    have h2 : eval₂ (Int.castRingHom _) formPoly f = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h1
    have h3 := congrArg (eval₂Hom σ v) h2
    rw [map_zero, map_eval₂_int] at h3
    have hz : (eval₂Hom σ v) ∘ formPoly = projPlanePt σ v := funext (eval₂_formPoly σ v)
    rw [hz] at h3
    rw [eval_map]
    exact h3

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PProjPtsOnPlane
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace ProjectivePointsOnPlane

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def mulMat (α : 𝓞 K) (m n : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) : ℤ :=
  (RingOfIntegers.basis K).repr (α * RingOfIntegers.basis K m) n

theorem mulMat_sum (α : 𝓞 K) (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    ∑ n, (mulMat α m n : K) * integralBasis K n = (α : K) * integralBasis K m := by
  have h := congrArg (algebraMap (𝓞 K) K) ((RingOfIntegers.basis K).sum_repr
    (α * RingOfIntegers.basis K m))
  simp only [map_sum, map_mul, zsmul_eq_mul, map_intCast] at h
  simpa only [integralBasis_apply, mulMat, RingOfIntegers.coe_eq_algebraMap] using h

open scoped Classical in

theorem embComp_recon (u : (K →+* ℂ) → Fin i → ℂ) (τ : K →+* ℂ) :
    embComp τ (fun q : ProjIdx K i => ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * u σ q.2) = u τ := by
  set b := canonicalEmbedding.latticeBasis K
  have hd : ∀ σ : K →+* ℂ, ∑ m, b.repr (Pi.single τ 1) m * σ (integralBasis K m) =
      if σ = τ then 1 else 0 := by
    intro σ
    have h := congrFun (b.sum_repr (Pi.single τ 1)) σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b, canonicalEmbedding.latticeBasis_apply,
      canonicalEmbedding.apply_at, Pi.single_apply] at h
    exact h
  funext j
  calc embComp τ (fun q : ProjIdx K i => ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * u σ q.2) j
      = ∑ m, ∑ σ : K →+* ℂ, b.repr (Pi.single τ 1) m * (σ (integralBasis K m) * u σ j) := by
        simp only [embComp, Finset.mul_sum]; rfl
    _ = ∑ σ : K →+* ℂ, (∑ m, b.repr (Pi.single τ 1) m * σ (integralBasis K m)) * u σ j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = u τ j := by
        rw [Finset.sum_congr rfl fun σ _ => congrArg (· * u σ j) (hd σ)]
        simp

def lin (α : 𝓞 K) (Z : ProjIdx K i → ℂ) : ProjIdx K i → ℂ :=
  fun q => ∑ n, (mulMat α q.1 n : ℂ) * Z (n, q.2)

theorem lin_eq (α : 𝓞 K) (Z : ProjIdx K i → ℂ) (q : ProjIdx K i) :
    lin α Z q = ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * (σ (α : K) * embComp σ Z q.2) := by
  calc lin α Z q
      = ∑ n, ∑ σ : K →+* ℂ, (mulMat α q.1 n : ℂ) * (σ (integralBasis K n) * embComp σ Z q.2) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← sum_emb_embComp Z n q.2, Finset.mul_sum]
    _ = ∑ σ : K →+* ℂ, (∑ n, (mulMat α q.1 n : ℂ) * σ (integralBasis K n)) * embComp σ Z q.2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun n _ => by ring
    _ = _ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        have h := congrArg σ (mulMat_sum α q.1)
        simp only [map_sum, map_mul, map_intCast] at h
        rw [h]
        ring

theorem embComp_lin (α : 𝓞 K) (Z : ProjIdx K i → ℂ) (τ : K →+* ℂ) :
    embComp τ (lin α Z) = τ (α : K) • embComp τ Z := by
  have h : lin α Z = fun q : ProjIdx K i =>
      ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * (fun σ j => σ (α : K) * embComp σ Z j) σ q.2 :=
    funext fun q => lin_eq α Z q
  rw [h]
  exact embComp_recon (fun σ j => σ (α : K) * embComp σ Z j) τ

def lform (α : 𝓞 K) (q : ProjIdx K i) : MRing (projBlocks K i) :=
  ∑ n, C (mulMat α q.1 n) * X ⟨(), (n, q.2)⟩

def quad (α : 𝓞 K) (p q : ProjIdx K i) : MRing (projBlocks K i) :=
  X ⟨(), p⟩ * lform α q - lform α p * X ⟨(), q⟩

theorem quad_mem (α : 𝓞 K) (p q : ProjIdx K i) : quad α p q ∈ projSpaceIdeal K i := by
  have hlin : ∀ u : ProjIdx K i, ∑ n, (mulMat α u.1 n : MvPolynomial (Fin i) K) *
      (C (integralBasis K n) * X u.2) = C (α : K) * (C (integralBasis K u.1) * X u.2) := by
    intro u
    have h := congrArg (C : K → MvPolynomial (Fin i) K) (mulMat_sum α u.1)
    simp only [map_sum, map_mul, map_intCast] at h
    rw [← mul_assoc, ← h, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hS : ∀ u : ProjIdx K i, ∑ n, (mulMat α u.1 n : ProjField K i) * projSpaceCoord K i ⟨(), (n, u.2)⟩ =
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) * projSpaceCoord K i ⟨(), u⟩ := by
    intro u
    have h := congrArg (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) (hlin u)
    simpa only [projSpaceCoord, map_sum, map_mul, map_intCast] using h
  have hsum : ∀ u : ProjIdx K i, mConeMap (projSpaceCoord K i) (lform α u) =
      MvPolynomial.C (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) *
        projSpaceCoord K i ⟨(), u⟩) * MvPolynomial.X () := by
    intro u
    rw [← hS u, lform, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [mConeMap, aeval_X, map_mul, map_intCast, eq_intCast]
    ring
  show quad α p q ∈ RingHom.ker (mConeMap (projSpaceCoord K i))
  rw [RingHom.mem_ker]
  simp only [quad, map_sub, map_mul, hsum]
  simp only [mConeMap, aeval_X]
  ring

theorem eval_quad (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (α : 𝓞 K) (p q : ProjIdx K i) :
    eval z (map (Int.castRingHom ℂ) (quad α p q)) =
      z ⟨(), p⟩ * lin α (fun r => z ⟨(), r⟩) q - lin α (fun r => z ⟨(), r⟩) p * z ⟨(), q⟩ := by
  simp [quad, lform, lin]

theorem agree (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (hz : z ∈ mcPts (projSpaceIdeal K i)) (α : 𝓞 K)
    (σ τ : K →+* ℂ) (j l : Fin i) (hσ : embComp σ (fun q => z ⟨(), q⟩) j ≠ 0)
    (hτ : embComp τ (fun q => z ⟨(), q⟩) l ≠ 0) : σ (α : K) = τ (α : K) := by
  obtain ⟨q0, hq0⟩ := hz.1 ()
  set Z : ProjIdx K i → ℂ := fun q => z ⟨(), q⟩ with hZ
  have hrel : ∀ p q, Z p * lin α Z q = lin α Z p * Z q := by
    intro p q
    have h := hz.2 _ (quad_mem α p q)
    rw [eval_quad] at h
    exact sub_eq_zero.mp h
  have hL : lin α Z = (lin α Z q0 / Z q0) • Z := by
    funext r
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hq0]
    linear_combination hrel q0 r
  have key : ∀ ρ : K →+* ℂ, ρ (α : K) • embComp ρ Z = (lin α Z q0 / Z q0) • embComp ρ Z := by
    intro ρ
    rw [← embComp_lin, ← embComp_smul, ← hL]
  have h1 := congrFun (key σ) j
  have h2 := congrFun (key τ) l
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [mul_right_cancel₀ hσ h1, mul_right_cancel₀ hτ h2]

end ProjectivePointsOnPlane

open ProjectivePointsOnPlane in

theorem ProjPtsOnPlane.proof : ProjPtsOnPlane.Statement := by
  intro K _ _ i z hz
  obtain ⟨⟨m0, j0⟩, hq0⟩ := hz.1 ()
  obtain ⟨σ, j, hσ⟩ : ∃ (σ : K →+* ℂ) (j : Fin i), embComp σ (fun q => z ⟨(), q⟩) j ≠ 0 := by
    by_contra hne
    simp only [ne_eq, not_exists, not_not] at hne
    exact hq0 ((sum_emb_embComp (fun q => z ⟨(), q⟩) m0 j0).symm.trans (by simp [hne]))
  refine ⟨σ, fun τ hτ => ?_⟩
  funext l
  by_contra hne
  apply hτ
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
  ext α
  exact agree z hz α τ σ l j hne hσ

end

end GroundTheory.Heights₂.Heights
end

