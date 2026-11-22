import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonomialOfClean
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumCompletionEqColumnTestFunction
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.LastStepProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hat_coset_of_not [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : valuation k ε = 1) (y₀ : n → k) {η : n → k} (hη : ¬ ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀)) η = 0 := by
  classical
  have := hν.1
  have := secondCountable k
  have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) =
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x := fun z hz x => by
    have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq _).2 (by simpa using hz)
    simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
  refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
    (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
  · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

theorem topAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → TopAgree Ch sel mu cst σ₀ P ι S ν := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν hA e' e he' he
  refine ⟨1, one_ne_zero, fun y y' hy' => ?_⟩
  have hm : R.m = s + 2 := hA.steps
  have hT := hA.tie
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hT.compl.int
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hNpos : R.N R.m - 1 < R.N R.m := by have := (e (Sum.inr ())).isLt; omega

  have hq : (qOf P.1 : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot
  set η' := atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hη'
  have hη'v : ∀ v, η' v = y v (e (Sum.inr ())) := fun v => by
    simp only [hη', LinearMap.comp_apply, atNL, dif_pos hNpos, LinearMap.proj_apply]
    rw [show (⟨R.N R.m - 1, hNpos⟩ : Fin (R.N R.m)) = e (Sum.inr ()) from Fin.ext hlast.symm]
  have hrow : (toLoc ι e e' y) (Sum.inr ()) = fun a => ι (η' (Pi.single (e' a) 1)) := by
    funext a; simp [toLoc, hη'v]
  have hsum : η' y' = ∑ i, y' i * η' (Pi.single i 1) := by
    have : y' = ∑ i, y' i • Pi.single i (1 : X.E) := by ext j; simp [Pi.single_apply]
    conv_lhs => rw [this]
    simp [map_sum, map_smul]
  have hdot : (fun a => ι (η' (Pi.single (e' a) 1))) ⬝ᵥ (fun a => ι (y' (e' a))) = ι (η' y') := by
    rw [hsum, map_sum, dotProduct]
    exact Fintype.sum_equiv e' _ _ (fun a => by simp [mul_comm])
  have hB : hat S.ψ ν (-1) (cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk fun a => ι (y' (e' a))))
      ((toLoc ι e e' y) (Sum.inr ())) = σ₀ (ftY sel mu cst P η' y') := by
    rw [hrow, ftY, if_pos hA.mem]
    by_cases hη : ∀ i : Fin (R.N (s + 1)), IntAt P.1 (η' (Pi.single i 1))
    · rw [if_pos hη, GlobalTheory.StepData.Model.hat_coset S.cond hν (neg_mem (one_mem _)) _
        (fun a => (hint _).2 (hη _)), hdot]
      have hi : IntAt P.1 ((qOf P.1 : X.E) * ((epsSg : X.E) * η' y')) := by
        rw [← hint, hsum]
        have : (qOf P.1 : X.E) * ((epsSg : X.E) * ∑ i, y' i * η' (Pi.single i 1)) =
            -∑ i, ((qOf P.1 : X.E) * y' i) * η' (Pi.single i 1) := by
          simp only [epsSg, Int.cast_neg, Int.cast_one, Finset.mul_sum]; ring_nf; simp [Finset.sum_neg_distrib]
        rw [this, map_neg, map_sum]
        exact neg_mem (sum_mem fun i _ => by rw [map_mul]; exact mul_mem ((hint _).2 (hy' i)) ((hint _).2 (hη i)))
      have h1 := hT.psi _ hi
      have h2 := hA.psi0 _ hi
      rw [mul_div_cancel_left₀ _ hq] at h1 h2
      rw [h2, ← h1]
      simp [epsSg]
    · rw [if_neg hη, map_zero]
      exact LastStepProof.hat_coset_of_not S.cond hν (by simp) _
        fun h => hη fun i => by simpa using (hint _).1 (h (e'.symm i))

  have hc : cOf R (s + 1) = 0 := by unfold cOf; omega
  have hρ : R.rS = S.ρ := by have := S.odd; unfold Ranks.rS; omega
  have hr : R.r = R.k + s + 1 := by unfold Ranks.r; omega
  have hN : R.N R.m - 1 = R.k + s + 1 + (s + 2) * R.t := by
    unfold Ranks.N; rw [hm]
    have : (s + 2) * (R.t + 1) = (s + 2) * R.t + (s + 2) := by ring
    omega
  let E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))
  have hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0 := fun z => by
    have h1 := (e (Sum.inl z)).isLt
    have h2 : e (Sum.inl z) ≠ e (Sum.inr ()) := e.injective.ne (by simp)
    have h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1 := fun h => h2 (Fin.ext (h.trans hlast.symm))
    omega
  let f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0) := fun z => ⟨(e (Sum.inl z)).val, hbd z⟩
  have hf1 : Function.Bijective f1 := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩
    · have h' := Fin.val_eq_of_eq h
      have : e (Sum.inl z) = e (Sum.inl z') := Fin.ext h'
      exact Sum.inl_injective (e.injective this)
    · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      omega
  let E1 := Equiv.ofBijective f1 hf1
  have hE1' : IsOrd (yPos xPos (R.N (s + 1))) E1' := by
    rintro (a | a)
    · exact he' a
    · exact a.elim0
  have hE1 : IsOrd zPos E1 := fun z => he (Sum.inl z)
  have hPT := GlobalTheory.T.lastStep_testFunctions_agree_rationalPoints X.E X.K k P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) s R.k S hT R.t (R.N (s + 1))
    (cOf R (s + 1)) (R.N R.m - 1) rfl hc hN E1' E1 hE1' hE1
  have hmat : fromCols (toLoc ι e e' y).toRows₁ 0 =
      toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) := by
    ext z c
    rcases c with c | c
    · simp only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]
      have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) =
          Pi.single (e' c) 1 := by
        funext i
        simp [E1', Pi.single_apply, Fin.ext_iff]
      rw [hs]
      rfl
    · exact c.elim0
  have hkey : ∀ c' n' c n : ℕ, LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t R.m c' n' c n =
      LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k S.ρ (R.k + s + 1) R.t (s + 2) c' n' c n := by
    intro c' n' c n; rw [hρ, hr, hm]
  have hA' : (S.T (Fin R.t)).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
      σ₀ (PhiTop Ch mu cst.sharp s P.1
        (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
    rw [hmat, hPT, PhiTop, if_pos hA.mem, hA.sharp, if_pos rfl, hkey]
  simp only [Chain.xiTop]
  rw [one_mul, map_mul, hA', hB]

end GlobalTheory.SymBridge.LastStepProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportParahoricBiTransformingLeviDoubleCoset
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem diagT_mem_parahoric (c : A ⊕ D → kˣ) (hc : ∀ i, valuation k (c i : k) = 1) :
    diagT k (A ⊕ D) c ∈ parahoric k A D := by
  rw [mem_parahoric]
  refine ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [val_diagT, diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 (hc i).le
    · exact zero_mem _
  · rw [← map_inv, val_diagT, diagonal_apply]
    split_ifs
    · refine (Valuation.mem_integer_iff _ _).2 ?_
      simp [map_inv₀, hc i]
    · exact zero_mem _
  · rw [val_diagT, diagonal_apply_ne _ (by simp)]
    simp

theorem det_lower_diagT (c : A ⊕ D → kˣ) :
    ((diagT k (A ⊕ D) c : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det =
      ((∏ i, c (.inr i) : kˣ) : k) := by
  have : ((diagT k (A ⊕ D) c : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂ =
      diagonal fun i => (c (.inr i) : k) := by
    ext i j
    simp [toBlocks₂₂, val_diagT, diagonal_apply]
  rw [this, det_diagonal, Units.coe_prod]

theorem prod_mulSingle_inr (p : A ⊕ D) (u : kˣ) :
    (∏ i : D, (Pi.mulSingle p u : A ⊕ D → kˣ) (.inr i)) = if p.isRight then u else 1 := by
  rcases p with a | d
  · simp [Pi.mulSingle_apply]
  · simp [Pi.mulSingle_apply]

end GlobalTheory.ParHeckeSupp

namespace GlobalTheory.ParHeckeSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem eq_zero_of_mixed (ξ : kˣ →* ℂˣ) (hξ : ¬ IsUnram ξ) (φ : GL (A ⊕ D) k → ℂ) (hφ : IsBiType ξ φ)
    (m : GL (A ⊕ D) k) (τ : Equiv.Perm (A ⊕ D)) (hm : ∀ x y, y ≠ τ x → (m : Matrix (A ⊕ D) (A ⊕ D) k) x y = 0)
    (p : A ⊕ D) (hp : (τ p).isRight ≠ p.isRight) : φ m = 0 := by
  obtain ⟨u, hu1, hu⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ξ u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hξ h
  have hv : ∀ q : A ⊕ D, ∀ i, valuation k ((Pi.mulSingle q u : A ⊕ D → kˣ) i : k) = 1 := fun q i => by
    rw [Pi.mulSingle_apply]
    split_ifs <;> simp [hu1]
  have hcomm : diagT k (A ⊕ D) (Pi.mulSingle p u) * m = m * diagT k (A ⊕ D) (Pi.mulSingle (τ p) u) := by
    ext x y
    simp only [Units.val_mul, val_diagT, diagonal_mul, mul_diagonal]
    by_cases hy : y = τ x
    · subst hy
      simp [Pi.mulSingle_apply, mul_comm]
    · simp [hm x y hy]
  have h1 := (hφ _ (diagT_mem_parahoric _ (hv p)) _ (det_lower_diagT _).symm m).1
  have h2 := (hφ _ (diagT_mem_parahoric _ (hv (τ p))) _ (det_lower_diagT _).symm m).2
  rw [hcomm, h2, prod_mulSingle_inr, prod_mulSingle_inr] at h1
  have hu' : (ξ u : ℂ) ≠ 1 := fun h => hu (Units.ext (by simpa using h))
  by_contra h0
  have h3 := mul_right_cancel₀ h0 h1
  cases h₁ : (τ p).isRight <;> cases h₂ : p.isRight <;> simp only [h₁, h₂] at h3 hp
  · exact hp rfl
  · exact hu' (by simpa using h3.symm)
  · exact hu' (by simpa using h3)
  · exact hp rfl

theorem exists_emb₂ (m : GL (A ⊕ D) k) (τ : Equiv.Perm (A ⊕ D))
    (hm : ∀ x y, y ≠ τ x → (m : Matrix (A ⊕ D) (A ⊕ D) k) x y = 0) (hτ : ∀ p, (τ p).isRight = p.isRight) :
    ∃ x y, m = emb₂ k (Equiv.refl (A ⊕ D)) (x, y) := by
  have h12 : (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₁₂ = 0 := by
    ext a d
    refine hm _ _ fun h => ?_
    have := hτ (.inl a)
    rw [← h] at this
    simp at this
  have h21 : (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₁ = 0 := by
    ext d a
    refine hm _ _ fun h => ?_
    have := hτ (.inr d)
    rw [← h] at this
    simp at this
  have hdet : (m : Matrix (A ⊕ D) (A ⊕ D) k).det =
      (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₁₁.det * (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det := by
    conv_lhs => rw [← fromBlocks_toBlocks (m : Matrix (A ⊕ D) (A ⊕ D) k), h12]
    exact det_fromBlocks_zero₁₂ _ _ _
  have hm0 : (m : Matrix (A ⊕ D) (A ⊕ D) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  rw [hdet] at hm0
  refine ⟨nonsingInvUnit _ (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul hm0)),
    nonsingInvUnit _ (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hm0)), Units.ext ?_⟩
  rw [val_emb₂]
  simp only [reindex_refl_refl]
  conv_lhs => rw [← fromBlocks_toBlocks (m : Matrix (A ⊕ D) (A ⊕ D) k), h12, h21]
  rfl

end GlobalTheory.ParHeckeSupp

namespace GlobalTheory.ParHeckeSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def numE : A ⊕ D ≃ Fin (Fintype.card A + Fintype.card D) :=
  (Equiv.sumCongr (Fintype.equivFin A) (Fintype.equivFin D)).trans finSumFinEquiv

theorem numE_lt (a : A) (d : D) : numE (A := A) (D := D) (.inl a) < numE (.inr d) := by
  simp only [numE, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_iff_val_lt_val, Fin.coe_castAdd,
    Fin.coe_natAdd]
  omega

variable (k A D) in

def toAD : GL (Fin (Fintype.card A + Fintype.card D)) k →* GL (A ⊕ D) k :=
  Units.map (reindexAlgEquiv k k (numE (A := A) (D := D)).symm).toMonoidHom

theorem toAD_val (g : GL (Fin (Fintype.card A + Fintype.card D)) k) (x y : A ⊕ D) :
    (toAD k A D g : Matrix (A ⊕ D) (A ⊕ D) k) x y = (g : Matrix _ _ k) (numE x) (numE y) := by
  simp [toAD, reindexAlgEquiv_apply, reindex_apply]

theorem toAD_surj (g : GL (A ⊕ D) k) : ∃ g₀, toAD k A D g₀ = g :=
  ⟨Units.map (reindexAlgEquiv k k (numE (A := A) (D := D))).toMonoidHom g,
    Units.ext (Matrix.ext fun x y => by rw [toAD_val]; simp [reindexAlgEquiv_apply, reindex_apply])⟩

theorem toAD_incl_mem (u : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.unipLevel k (Fintype.card A + Fintype.card D)) :
    toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u) ∈ parahoric k A D := by
  rw [mem_parahoric]
  refine ⟨⟨Units.map (reindexAlgEquiv 𝒪[k] 𝒪[k] (numE (A := A) (D := D)).symm).toMonoidHom u.1, ?_⟩,
    fun i j => ?_⟩
  · ext x y
    rw [toAD_val, GlobalTheory.TypeDim.incl_val]
    simp [reindexAlgEquiv_apply, reindex_apply]
    rfl
  · rw [toAD_val, GlobalTheory.TypeDim.incl_val]
    have h := ((mem_unipB _).1 (Subgroup.mem_comap.1 u.2)).1 _ _ (numE_lt j i)
    rw [GlobalTheory.TypeDim.red_val] at h
    exact (GlobalTheory.ParahoricLowerBlock.residue_eq_zero_iff_val _).1 h

theorem support_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ →
    ∀ φ : GL (A ⊕ D) k → ℂ, IsBiType ξ φ → ∀ g, φ g ≠ 0 → ∃ x y, ∃ j ∈ parahoric k A D,
      ∃ j' ∈ parahoric k A D, g = j * emb₂ k (Equiv.refl (A ⊕ D)) (x, y) * j' := by
  intro k _ _ _ _ A D _ _ _ _ ξ hξt hξ φ hφ g hg
  obtain ⟨g₀, rfl⟩ := toAD_surj g
  obtain ⟨u, u', w, c, e⟩ := GlobalTheory.TypeDim.IwahoriBruhat.iwahori_bruhat k _ g₀
  have hj := toAD_incl_mem (A := A) (D := D) u
  have hj' := toAD_incl_mem (A := A) (D := D) u'
  have hgm : toAD k A D g₀ = toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u) *
      toAD k A D (GlobalTheory.Parabolic.permGL k w * diagT k _ c) * toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u') := by
    rw [e]
    simp only [map_mul]
  generalize toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u) = j at hj hgm
  generalize toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u') = j' at hj' hgm
  let τ : Equiv.Perm (A ⊕ D) := numE.trans (w.symm.trans numE.symm)
  have hm : ∀ x y, y ≠ τ x →
      (toAD k A D (GlobalTheory.Parabolic.permGL k w * diagT k _ c) : Matrix (A ⊕ D) (A ⊕ D) k) x y = 0 := by
    intro x y h
    rw [toAD_val, Units.val_mul, val_diagT, mul_diagonal, GlobalTheory.Parabolic.permGL_apply, if_neg, zero_mul]
    intro h'
    apply h
    simp [τ, h']
  generalize toAD k A D (GlobalTheory.Parabolic.permGL k w * diagT k _ c) = m at hm hgm
  have hφm : φ m ≠ 0 := by
    intro h0
    apply hg
    obtain ⟨hd, -⟩ := GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D ξ hξt j hj
    obtain ⟨hd', -⟩ := GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D ξ hξt j' hj'
    rw [hgm, (hφ j' hj' (Units.mk0 _ hd') rfl _).2, (hφ j hj (Units.mk0 _ hd) rfl _).1, h0]
    simp
  have hτ : ∀ p, (τ p).isRight = p.isRight := by
    by_contra h
    push_neg at h
    obtain ⟨p, hp⟩ := h
    exact hφm (eq_zero_of_mixed ξ hξ φ hφ m τ hm p hp)
  obtain ⟨x, y, hxy⟩ := exists_emb₂ m τ hm hτ
  exact ⟨x, y, j, hj, j', hj', by rw [hgm, hxy]⟩

end GlobalTheory.ParHeckeSupp
end
end

