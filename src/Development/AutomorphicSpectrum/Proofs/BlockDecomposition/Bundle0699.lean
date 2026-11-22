import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianAdeles
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockInverseIntegralIff
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem blk_inv_val {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    ((blk h w m X)⁻¹).val =
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) := by
  have a1 : m.1.val * (m.1⁻¹).val = 1 := Units.mul_inv m.1
  have a2 : (m.1⁻¹).val * m.1.val = 1 := Units.inv_mul m.1
  have b1 : m.2.val * (m.2⁻¹).val = 1 := Units.mul_inv m.2
  have b2 : (m.2⁻¹).val * m.2.val = 1 := Units.inv_mul m.2
  have h1 : fromBlocks m.1.val (m.1.val * X) 0 m.2.val *
      fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [a1]
    · simp [Matrix.mul_assoc]
    · simp
    · simp [b1]
  have h2 : fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val *
      fromBlocks m.1.val (m.1.val * X) 0 m.2.val = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [a2]
    · simp [← Matrix.mul_assoc, a2, Matrix.mul_assoc, b2]
    · simp
    · simp [b2]
  have r1 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) *
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) = 1 := by
    simp only [reindex_apply, submatrix_mul_equiv, h1, submatrix_one_equiv]
  have r2 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) *
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) = 1 := by
    simp only [reindex_apply, submatrix_mul_equiv, h2, submatrix_one_equiv]
  have hU : IsUnit (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := ⟨⟨_, _, r1, r2⟩, rfl⟩
  have hb : (blk h w m X).val = reindex (finSumFinEquiv.trans (finCongr h))
      (finSumFinEquiv.trans (finCongr h)) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
    unfold blk
    simp only []
    rw [dif_pos hU]
    rfl
  exact Units.inv_eq_of_mul_eq_one_right (by rw [hb]; exact r1)

theorem isInt_smul_blk_inv_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (ϖ • ((blk h w m X)⁻¹).val) ↔ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val)) := by
  intro E _ _ _ n a b h w ϖ m X
  rw [blk_inv_val h w m X]
  constructor
  · intro H
    have key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w := by
      intro i j
      have := H (finSumFinEquiv.trans (finCongr h) i) (finSumFinEquiv.trans (finCongr h) j)
      simpa [reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using this
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.smul_apply, smul_eq_mul] using key (Sum.inl i) (Sum.inl j)
    · simpa [Matrix.smul_apply, smul_eq_mul] using key (Sum.inr i) (Sum.inr j)
    · have := (Ov E w).neg_mem (key (Sum.inl i) (Sum.inr j))
      simpa [Matrix.smul_apply, smul_eq_mul] using this
  · rintro ⟨H1, H2, H3⟩ i j
    have key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w := by
      rintro (i | i) (j | j)
      · simpa [Matrix.smul_apply, smul_eq_mul] using H1 i j
      · have := (Ov E w).neg_mem (H3 i j)
        simpa [Matrix.smul_apply, smul_eq_mul] using this
      · simpa using (Ov E w).zero_mem
      · simpa [Matrix.smul_apply, smul_eq_mul] using H2 i j
    simpa [reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using
      key ((finSumFinEquiv.trans (finCongr h)).symm i) ((finSumFinEquiv.trans (finCongr h)).symm j)

end GlobalTheory.CompanionTheory.CtS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermHeckeFormula
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have key : ∀ S : Subgroup H, S = ⊤ → ((S.index : ℂ))⁻¹ * ∑ᶠ _ : H ⧸ S, c = c := by
    rintro S rfl
    haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (H ⧸ (⊤ : Subgroup H)) := Unique.mk' _
    rw [finsum_unique, Subgroup.index_top]
    simp
  exact key _ (by ext k; simp [rStab])

theorem ctT_split_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E), IsSplitAt w → IsUnifV E w ϖ → ∀ (k : ℕ) (m : GLw a w × GLw b w), ctT h w ν ϖ k m = (ν ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) fun X => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) := by
  intro E _ _ _ n a b h w ν ϖ hw hϖ k m
  have hT : UL n w = ⊤ := if_pos hw
  have hv : ∀ y : GLw n w, ((toSub (UL n w) y : UL n w) : GLw n w) = y := fun y => by
    have hy : y ∈ UL n w := hT ▸ Subgroup.mem_top y
    simp [toSub, hy]
  have hc : ∀ (x : GLw n w) (g : GlobalTheory.LFun.KGL w n),
      Tj ℂ n (Ov E w) ϖ k ((g : GLw n w)⁻¹ * x * g) = Tj ℂ n (Ov E w) ϖ k x := fun x g =>
    (Tj_mem_hecke (n := n) hϖ k).1 g⁻¹ g x
  unfold ctT ctMu ct
  congr 2
  congr 1
  funext X
  simp only [hv, hc]
  exact avg_const _

end GlobalTheory.CompanionTheory.CtS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis

section Conj

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conj_isom_iff (c : R →+* R) (B g : GL ι R) (D J : Matrix ι ι R)
    (h : (B : Matrix ι ι R)ᵀ * D * (B : Matrix ι ι R).map c = J) :
    (((B⁻¹ * g * B : GL ι R) : Matrix ι ι R)ᵀ * J * ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R).map c = J) ↔
      (g : Matrix ι ι R)ᵀ * D * (g : Matrix ι ι R).map c = D := by
  have h1 : (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have h2 : (B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c)]
  have h1' : (B : Matrix ι ι R)ᵀ * (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  have h2' : ((B⁻¹ : GL ι R) : Matrix ι ι R).map c * (B : Matrix ι ι R).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c)]
  have key : ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R)ᵀ * J * ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R).map c =
      (B : Matrix ι ι R)ᵀ * ((g : Matrix ι ι R)ᵀ * D * (g : Matrix ι ι R).map c) * (B : Matrix ι ι R).map c := by
    subst h
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.map_mul]
    calc _ = (B : Matrix ι ι R)ᵀ * (g : Matrix ι ι R)ᵀ * ((((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ) * D *
          ((B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) * (g : Matrix ι ι R).map c *
          (B : Matrix ι ι R).map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [key]
  constructor
  · intro e
    have e' := congrArg (fun M => (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * M * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) e
    subst h
    have l : ∀ M : Matrix ι ι R, (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * ((B : Matrix ι ι R)ᵀ * M * (B : Matrix ι ι R).map c) *
        ((B⁻¹ : GL ι R) : Matrix ι ι R).map c = M := fun M => by
      calc _ = ((((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ) * M *
            ((B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [l] at e'
    rw [e', l]
  · intro e
    rw [e, h]

end Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def bA (b : GL (Fin n ⊕ Fin n) E) : GL (Fin n ⊕ Fin n) (AE F E) :=
  Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)) b

theorem bA_val (b : GL (Fin n ⊕ Fin n) E) :
    ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = incM F b.1 := rfl

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR]

theorem gram_frame (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ *
        dbl (incM F Y.J) * ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).map
          (adCM σ χ).σ = Ad.J (AE F E) ε (Fin n) := by
  have := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => M.map (inclR (F := F) (E := E) (AF F))) hb
  have e1 : (bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)).1.map (adCM σ χ).σ = (b.1.map σ).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    exact cA_inclR σ _
  have e2 : dbl (incM F Y.J) = (dbl Y.J).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl, incM]
  have e3 : (bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)).1ᵀ = (b.1ᵀ).map (inclR (F := F) (E := E) (AF F)) := rfl
  have e4 : Ad.J (AE F E) ε (Fin n) = (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;> simp [Ad.J, h, Matrix.one_apply]
  rw [e1, e2, e3, e4, ← this]
  simp only [Matrix.map_mul]

def frameEquiv (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    G2 σ Y ≃* (adCM σ χ).U ε (Fin n) where
  toFun x := ⟨(bA b)⁻¹ * x.1 * bA b, (conj_isom_iff (adCM σ χ).σ (bA b) x.1 _ _ (gram_frame χ ε b hb)).2 x.2⟩
  invFun y := ⟨bA b * y.1 * (bA b)⁻¹, by
    have h := (conj_isom_iff (adCM σ χ).σ (bA (F := F) b) (bA b * y.1 * (bA b)⁻¹) _ _ (gram_frame χ ε b hb)).1
    apply h
    have : (bA (F := F) b)⁻¹ * (bA b * y.1 * (bA b)⁻¹) * bA b = y.1 := by group
    rw [this]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    show bA b * ((bA b)⁻¹ * x.1 * bA b) * (bA b)⁻¹ = x.1
    group
  right_inv y := by
    apply Subtype.ext
    show (bA b)⁻¹ * (bA b * y.1 * (bA b)⁻¹) * bA b = y.1
    group
  map_mul' x y := by
    apply Subtype.ext
    show (bA b)⁻¹ * (x.1 * y.1) * bA b = ((bA b)⁻¹ * x.1 * bA b) * ((bA b)⁻¹ * y.1 * bA b)
    group

theorem frameEquiv_val (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (x : G2 σ Y) :
    (frameEquiv χ ε b hb x).1 = (bA b)⁻¹ * x.1 * bA b := rfl

theorem frameEquiv_symm_val (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (y : (adCM σ χ).U ε (Fin n)) :
    ((frameEquiv χ ε b hb).symm y).1 = bA b * y.1 * (bA b)⁻¹ := rfl

theorem continuous_frameEquiv (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    Continuous (frameEquiv χ ε b hb) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem continuous_frameEquiv_symm (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    Continuous (frameEquiv χ ε b hb).symm := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end GlobalTheory.CompanionTheory.SiegelFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionSmoothLieDerivative
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def psi (v : GA E a) : Lie E a := toL (GeneralLinearGroup.map (pInf E) v⁻¹).val

def wt (U : Subgroup (GL (Fin a) (Af E))) (F : GA E a → ℂ) (g : GA E a) : GA E a → ℂ :=
  Set.indicator {v | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U} fun v => F (g * v)

open Classical in

theorem wt_apply (U : Subgroup (GL (Fin a) (Af E))) (F : GA E a → ℂ) (g v : GA E a) :
    wt U F g v = if GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U then F (g * v) else 0 := by
  simp only [wt, Set.indicator_apply, Set.mem_setOf_eq]

def hb (β : Lie E a → ℂ) (q : Lie E a × Lie E a) : ℂ := β (toL (Matrix.of q.2 * Matrix.of q.1))

theorem continuous_psi : Continuous (psi (E := E) (a := a)) :=
  ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((ContAut.continuous_map_pInf E a).comp continuous_inv))

theorem contDiff_mul_lie : ContDiff ℝ ∞ fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e : (fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) i j) =
      fun q => ∑ k, q.2 i k * q.1 k j := by
    funext q; simp [toL, Matrix.mul_apply]
  rw [e]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ _ k).comp ((contDiff_apply ℝ _ i).comp contDiff_snd)).mul
      ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_fst))

theorem contDiff_hb {β : Lie E a → ℂ} (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (hb (E := E) (a := a) β) :=
  hβ.comp contDiff_mul_lie

end GlobalTheory.CompanionTheory.SmoothRep.TstConv

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_compact_of_mul_mem_tsupport : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ), IsTest β →
    ∀ x₀ ∈ invSet E a, ∃ Kc : Set (Lie E a), IsCompact Kc ∧ Kc ⊆ invSet E a ∧ ∃ N ∈ 𝓝 x₀,
      ∀ y x : Lie E a, x ∈ N → toL (Matrix.of y * Matrix.of x) ∈ tsupport β → y ∈ Kc := by
  intro E _ _ _ a β hβ x₀ hx₀
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) x₀ hx₀
  set N := Metric.closedBall x₀ (δ / 2)
  have hNs : N ⊆ invSet E a := (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball
  have hNc : IsCompact N := isCompact_closedBall x₀ (δ / 2)
  have hN' := isCompact_setOf_toL_mem (E := E) (a := a) hNc hNs
  have hB' := isCompact_setOf_toL_mem (E := E) (a := a) hβ.compact hβ.support
  have hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Cinf E) => toL (p.1 * p.2⁻¹).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp (continuous_fst.mul continuous_snd.inv)
  refine ⟨_, (hB'.prod hN').image hcont, ?_, N, Metric.closedBall_mem_nhds x₀ (half_pos hδ), ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact val_mem_invSet _
  · intro y x hx hm
    obtain ⟨u, hu⟩ := hNs hx
    obtain ⟨b, hb⟩ := hβ.support hm
    refine ⟨(b, u), ⟨?_, ?_⟩, ?_⟩
    · change toL b.val ∈ tsupport β
      rw [hb]
      exact hm
    · change toL u.val ∈ N
      rw [hu]
      exact hx
    · change toL (b * u⁻¹).val = y
      have e : (b * u⁻¹).val = Matrix.of y := by
        rw [Units.val_mul, hb]
        change Matrix.of y * Matrix.of x * u⁻¹.val = Matrix.of y
        rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      rw [e]
      rfl

theorem measurableSet_integrableOn_wt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ Fl : GA E a → ℂ, LocallyIntegrable Fl μ →
    ∀ Kc : Set (Lie E a), IsCompact Kc → Kc ⊆ invSet E a → ∀ g : GA E a,
      MeasurableSet {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} ∧
      IntegrableOn (wt U Fl g) {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} μ := by
  intro E _ _ _ a μ _ U hU hUc Fl hFl Kc hKc hKs g
  have hS : IsOpen {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U} :=
    hU.preimage ((ContAut.continuous_map_pFin E a).comp continuous_inv)
  have hm : MeasurableSet {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} :=
    hS.measurableSet.inter (hKc.isClosed.preimage continuous_psi).measurableSet
  refine ⟨hm, ?_⟩
  have hK' := isCompact_setOf_toL_mem (E := E) (a := a) hKc hKs
  have hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹ :=
    ((GlobalTheory.CuspQuot.continuous_infGL.comp continuous_fst).mul
      ((GlobalTheory.BlockLevel.continuous_finGL a).comp continuous_snd)).inv
  have hD := (hK'.prod hUc).image hcont
  have hCD : {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} ⊆
      (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹) ''
        ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ (U : Set (GL (Fin a) (Af E)))) := by
    rintro v ⟨hvU, hvK⟩
    exact ⟨(GeneralLinearGroup.map (pInf E) v⁻¹, GeneralLinearGroup.map (pFin E) v⁻¹), ⟨hvK, hvU⟩,
      by simp only [infGL_mul_finGL, inv_inv]⟩
  have hDg := hD.image (continuous_const_mul g)
  have hi : IntegrableOn (fun v => Fl (g * v)) ((fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) =>
      (infGL E a p.1 * finGL E a p.2)⁻¹) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ
        (U : Set (GL (Fin a) (Af E))))) μ := by
    have := ((measurePreserving_mul_left μ g).integrableOn_comp_preimage
      (MeasurableEquiv.mulLeft g).measurableEmbedding).2 (hFl.integrableOn_isCompact hDg)
    rwa [Set.preimage_image_eq _ (mul_right_injective g)] at this
  exact (hi.mono_set hCD).indicator hS.measurableSet

theorem convR_tst_mul_infGL (μ : Measure (GA E a)) [μ.IsMulLeftInvariant] (U : Subgroup (GL (Fin a) (Af E)))
    (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    convR μ (tst U β) Fl (g * infGL E a y) = ∫ v, hb β (toL y.val, psi v) * wt U Fl g v ∂μ := by
  rw [← integral_mul_left_eq_self (fun v => hb β (toL y.val, psi v) * wt U Fl g v) (infGL E a y)]
  unfold convR
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hf : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pFin E) v⁻¹ := by
    simp [_root_.mul_inv_rev, map_mul, map_inv]
  have hi : GeneralLinearGroup.map (pInf E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pInf E) v⁻¹ * y⁻¹ := by
    simp [_root_.mul_inv_rev, map_mul, map_inv]
  show _ = hb β (toL y.val, psi (infGL E a y * v)) * wt U Fl g (infGL E a y * v)
  rw [wt_apply]
  by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
  · have h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∈ U := hf ▸ h
    simp only [tst, ker, if_pos h, if_pos h', hb, psi, hi]
    simp [toL, mul_assoc]
  · have h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∉ U := hf ▸ h
    simp only [tst, ker, if_neg h, if_neg h']
    simp
end GlobalTheory.CompanionTheory.SmoothRep.TstConv

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem fderiv_hb_one {β : Lie E a → ℂ} (hβ : ContDiff ℝ ∞ β) (y X : Lie E a) :
    fderiv ℝ (fun q => hb β (q, y)) (oneL E a) X = dTest X β y := by
  have e : (fun q => hb β (q, y)) = β ∘ lmul y := rfl
  have e1 : lmul y (oneL E a) = y := mul_one (Matrix.of y)
  rw [e, fderiv_comp _ (by rw [e1]; exact (hβ.differentiable (by simp)).differentiableAt)
    (lmul y).differentiableAt, e1, ContinuousLinearMap.fderiv]
  rfl

theorem exists_local {μ : Measure (GA E a)} [μ.IsHaarMeasure] {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) (g : GA E a)
    {x₀ : Lie E a} (hx₀ : x₀ ∈ invSet E a) :
    ∃ C : Set (GA E a), ∃ K : Set (Lie E a), ∃ N ∈ 𝓝 x₀, MeasurableSet C ∧ IsCompact K ∧ (∀ v ∈ C, psi v ∈ K) ∧
      IntegrableOn (wt U Fl g) C μ ∧
      ∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N, toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β := by
  obtain ⟨Kc, hKc, hKs, N, hN, hNK⟩ := exists_compact_of_mul_mem_tsupport E a β hβ x₀ hx₀
  obtain ⟨hCm, hCi⟩ := measurableSet_integrableOn_wt E a μ U hU hUc Fl hFl Kc hKc hKs g
  exact ⟨_, Kc, N, hN, hCm, hKc, fun v hv => hv.2, hCi, fun v hv hvU x hx hm => hv ⟨hvU, hNK _ _ hx hm⟩⟩

theorem integrand_eq_zero {U : Subgroup (GL (Fin a) (Af E))} {β : Lie E a → ℂ} {Fl : GA E a → ℂ} {g : GA E a}
    {C : Set (GA E a)} {N : Set (Lie E a)}
    (hC : ∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N, toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β)
    {x : Lie E a} (hx : x ∈ N) (v : GA E a) (hv : v ∉ C) : hb β (x, psi v) * wt U Fl g v = 0 := by
  rw [wt_apply]
  by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
  · rw [hb, image_eq_zero_of_notMem_tsupport (hC v hv h x hx), zero_mul]
  · rw [if_neg h, mul_zero]

end GlobalTheory.CompanionTheory.SmoothRep.TstConv

open GlobalTheory.CompanionTheory.SmoothRep.TstConv in

theorem GlobalTheory.CompanionTheory.SmoothRep.convR_tst_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β → ∀ Fl : GA E a → ℂ, LocallyIntegrable Fl μ → convR μ (tst U β) Fl ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a), lieD X (convR μ (tst U β) Fl) g = convR μ (tst U (dTest X β)) Fl g := by
  intro E _ _ _ a μ _ _ U hU hUc β hβ Fl hFl

  have hchart : ∀ g, ∀ x ∈ invSet E a,
      chart (convR μ (tst U β) Fl) g x = ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ := by
    intro g x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    rw [chart_val, convR_tst_mul_infGL]
  have hev : ∀ g, ∀ x ∈ invSet E a, chart (convR μ (tst U β) Fl) g =ᶠ[𝓝 x]
      fun x => ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ := fun g x hx =>
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) (hchart g)

  have hloc : ∀ g, ∀ x₀ ∈ invSet E a, ∃ C : Set (GA E a), ∃ N ∈ 𝓝 x₀,
      (∀ x ∈ N, (∫ v, hb β (x, psi v) * wt U Fl g v ∂μ) = ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧
      ContDiff ℝ ∞ (fun x => ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧
      (∀ p X, fderiv ℝ (fun x => ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) p X =
        ∫ v in C, fderiv ℝ (fun q => hb β (q, psi v)) p X * wt U Fl g v ∂μ) ∧
      (∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N,
        toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β) := by
    intro g x₀ hx₀
    obtain ⟨C, K, N, hN, hCm, hK, hCK, hCi, hvan⟩ := exists_local hU hUc hβ hFl g hx₀
    have P := GlobalTheory.CompanionTheory.SmoothParam.contDiff_integral_density (GA E a) (Lie E a) (Lie E a) (μ.restrict C)
      (wt U Fl g) psi K hCi continuous_psi.aestronglyMeasurable hK
      ((ae_restrict_iff' hCm).2 (Filter.Eventually.of_forall hCK)) (hb β) (contDiff_hb hβ.contDiff)
    exact ⟨C, N, hN, fun x hx => (setIntegral_eq_integral_of_forall_compl_eq_zero
      (integrand_eq_zero hvan hx)).symm, P.1, P.2, hvan⟩
  refine ⟨fun g x hx => ?_, fun X g => ?_⟩
  · obtain ⟨C, N, hN, heq, hcd, -, -⟩ := hloc g x hx
    exact (hcd.contDiffAt.congr_of_eventuallyEq
      ((hev g x hx).trans (Filter.eventually_of_mem hN heq))).contDiffWithinAt
  · have h1 : oneL E a ∈ invSet E a := isUnit_one
    obtain ⟨C, N, hN, heq, hcd, hder, hvan⟩ := hloc g _ h1
    rw [lieD, ((hev g _ h1).trans (Filter.eventually_of_mem hN heq)).fderiv_eq, hder]
    simp_rw [fderiv_hb_one hβ.contDiff]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero ?_]
    · unfold convR
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      show dTest X β (psi v) * wt U Fl g v = tst U (dTest X β) v * Fl (g * v)
      rw [wt_apply]
      by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
      · simp only [tst, ker, if_pos h, psi]
      · simp only [tst, ker, if_neg h, mul_zero, zero_mul]
    · intro v hv
      rw [wt_apply]
      by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
      · have hn : psi v ∉ tsupport β := by
          have := hvan v hv h (oneL E a) (mem_of_mem_nhds hN)
          simpa [toL] using this
        have h0 : fderiv ℝ β (psi v) = 0 := by
          by_contra h0
          exact hn (support_fderiv_subset ℝ h0)
        rw [dTest, h0, ContinuousLinearMap.zero_apply, zero_mul]
      · rw [if_neg h, mul_zero]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianAdelesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfdual_measure_hermitian_adeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ ν : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermCoord.exists_sdHerm | exact GlobalTheory.CompanionTheory.SW.HermCoord.exists_sdHerm | (intros; apply GlobalTheory.CompanionTheory.SW.HermCoord.exists_sdHerm <;> assumption)
end

