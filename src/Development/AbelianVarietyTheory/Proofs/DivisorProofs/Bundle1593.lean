import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisLineDiffF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance isModTopAEF : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

theorem finiteDimensional_FE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

local instance : FiniteDimensional F E := finiteDimensional_FE

local instance topRingAEF : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_sigR_AF (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add a b ha hb => rw [map_add, LinearMap.map_add, ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

theorem map_trace_tens {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (p : R →ₐ[F] R')
    (y : R ⊗[F] E) :
    p (Algebra.trace R (R ⊗[F] E) y) =
      Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map p (AlgHom.id F E) y) := by
  have h1 : ∀ (S : Type) [CommRing S] [Algebra F S] (r : S) (x : E),
      Algebra.trace S (S ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F S (Algebra.trace F E x) := by
    intro S _ _ r x
    have h1 : Algebra.trace S (S ⊗[F] E) ((1 : S) ⊗ₜ[F] x) = algebraMap F S (Algebra.trace F E x) := by
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    have h2 : r ⊗ₜ[F] x = r • ((1 : S) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2, LinearMap.map_smul, h1, smul_eq_mul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h1, h1, map_mul, AlgHom.commutes]
  | add y y' hy hy' => simp only [map_add, hy, hy']

theorem finPartF_sigR (σ : E →ₐ[F] E) (z : AEF F E) :
    finPartF F E (sigR (AF F) σ z) = sigR (Af F) σ (finPartF F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

theorem sndA_symplOHF (ξ₀ : E) (w y : WOF F E nS nT) (hy : y.map (finPartF F E) = 0) :
    sndA F (symplOHF σ JS JT ξ₀ w y) = 0 := by
  have hk : ∀ a b c d, finPartF F E (incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) * w d a) = 0 := by
    intro a b c d
    have h0 : finPartF F E (y c b) = 0 := congrFun (congrFun hy c) b
    rw [map_mul, map_mul, map_mul, finPartF_sigR, h0, map_zero, mul_zero, zero_mul, zero_mul]
  have hh : finPartF F E (hOF σ JS JT w y) = 0 := by
    unfold hOF
    simp only [map_sum, hk, Finset.sum_const_zero]
  unfold symplOHF symplOF
  rw [map_mul, map_trace_tens]
  have e : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (incAF F E ξ₀ * hOF σ JS JT w y) =
      finPartF F E (incAF F E ξ₀ * hOF σ JS JT w y) := rfl
  rw [e, map_mul, hh, mul_zero, map_zero, mul_zero]

theorem symplOHF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x (y + y') = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplOHF_zero_right (ξ₀ : E) (x : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x 0 = 0 := by
  have := symplOHF_add_right σ JS JT ξ₀ x 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem continuous_symplOHF (ξ₀ : E) (w : WOF F E nS nT) {X : Type} [TopologicalSpace X] {y : X → WOF F E nS nT}
    (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT ξ₀ w (y t) := by
  have hy' : ∀ i j, Continuous fun t => cAF σ (y t i j) := fun i j =>
    (continuous_sigR_AF σ).comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hh : Continuous fun t => hOF σ JS JT w (y t) :=
    continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
      continuous_finset_sum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul continuous_const
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

theorem exists_log {Tau : Type} [Fintype Tau] {tauE : Tau → (E →+* ℂ)} {ψ : AddChar (AF F) ℂ}
    (hψ : IsStdCharF tauE ψ (-1)) :
    ∃ lam : AF F →+ ℂ, Continuous lam ∧ ∀ a, sndA F a = 0 → ψ a = Complex.exp (lam a) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  let lam : AF F →+ ℂ :=
    { toFun := fun a => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (fstA F a ⊗ₜ[F] (1 : E))
      map_zero' := by simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero, mul_zero]
      map_add' := fun a b => by simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  refine ⟨lam, ?_, fun a ha => ?_⟩
  · exact continuous_const.mul (continuous_finset_sum _ fun ρ _ => (hθ ρ).2.comp continuous_fst)
  · have hc := hψ.2.2 θ hθ (fstA F a)
    have e : pairA F (fstA F a) 0 = a := Prod.ext rfl ha.symm
    rw [psiInf, e] at hc
    exact hc

end GlobalTheory.HeisLineDiffF

open Formalism.IndefR.DatumF in

theorem GlobalTheory.HeisLineDiffF.differentiableAt_heisOF_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, DifferentiableAt ℝ (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log hψ
  let φ : ℝ →+ ℂ :=
    { toFun := fun t => lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun x y => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)
  let L' : (Fin 1 → ℝ) →+ WOF F E nS nT := L.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)
  have hL' : Continuous L' := hL.comp (continuous_apply 0)
  have hsm := hf.smooth 1 L' hL' (fun x => hL0 (x 0)) w
  have hg : ContDiff ℝ ∞ fun t : ℝ => f (w + L' (fun _ => t)) :=
    hsm.comp (contDiff_pi.2 fun _ => contDiff_id)
  have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f w) =
      fun t : ℝ => Complex.exp (φ t) * f (w + L' (fun _ => t)) := by
    funext t
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w (L t) (hL0 t))]
    rfl
  rw [e]
  have hd1 : DifferentiableAt ℝ (fun t : ℝ => Complex.exp (φ t)) 0 :=
    ((φ.toRealLinearMap hφ).differentiableAt).cexp
  exact hd1.mul ((hg.differentiable (by simp)) 0)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DblSchr

open Matrix GlobalTheory.Doubling

theorem dblGram_xi : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ξ • incM D.host.F (GlobalTheory.DblSchr.JBd S JB) = incM D.host.F (D.host.xi0 • (GlobalTheory.Doubling.dblSp S).gram⁻¹) := by
  intro D S JB ξ h
  have hinv : (dblSp S).gram⁻¹ = blkMat finSumFinEquiv S.gram⁻¹ (-S.gram⁻¹) :=
    Matrix.inv_eq_left_inv (by
      rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (isHermND_gram S).2.isUnit, blkMat_one])
  rw [hinv, incM_JBd]
  ext i j
  have hij : ∀ a b, ξ * incM D.host.F JB a b = incM D.host.F (D.host.xi0 • S.gram⁻¹) a b := fun a b => by
    rw [← h]; rfl
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp only [blkMat, GlobalTheory.WeilM.dbl, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, Matrix.smul_apply, Matrix.submatrix_apply, h1, h2,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, smul_zero, map_zero, smul_neg, map_neg, smul_eq_mul, mul_zero, mul_neg] at hij ⊢
  · exact hij i' j'
  · exact congrArg Neg.neg (hij i' j')

end GlobalTheory.DblSchr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqFinsetSumPureTensorCosetIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

theorem eq_sum_pureA_coset_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
    (K : Set (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact K →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
        (∀ r ∈ R, Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
          (∀ x, (fun i => (x i).2) ∉ K → Φ x = 0) →
            Φ = ∑ r ∈ R, GlobalTheory.WeilM.pureA F (GlobalTheory.WeilAdm.slice F Φ r) (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ U K hUo hUc hK
  classical
  have hcov : K ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ K, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  have hSB : ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    intro r
    have hcl : IsClopen {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      ⟨(AddSubgroup.isClosed_of_isOpen U hUo).preimage (continuous_id.sub continuous_const),
        hUo.preimage (continuous_id.sub continuous_const)⟩
    have hco : IsCompact {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      (Homeomorph.subRight r).isCompact_preimage.2 hUc
    refine ⟨?_, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U}
      · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_mem (show y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} from hy),
          Set.indicator_of_mem hx]
      · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
        simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)
  refine ⟨R, fun r _ => hSB r, fun Φ hinv hsupp => ?_⟩
  funext x
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, (fun i => (x i).2) - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have hm : (fun i => (x i).2) ∈ {y | y - r0 ∈ U} := hxr0
      simp only [GlobalTheory.WeilM.pureA, GlobalTheory.WeilAdm.slice, RingEquiv.symm_apply_apply, Set.indicator_of_mem hm, mul_one]
      obtain ⟨x', hx'⟩ : ∃ x' : κ → AdeleRing (𝓞 F) F, x' = fun i => ((x i).1, r0 i) := ⟨_, rfl⟩
      have e : x = x' + GlobalTheory.WeilAdm.finE F ((fun i => (x i).2) - r0) := by
        subst hx'
        funext i
        refine Prod.ext ?_ ?_
        · show (x i).1 = (x i).1 + 0
          rw [add_zero]
        · show (x i).2 = r0 i + ((x i).2 - r0 i)
          rw [add_sub_cancel]
      conv_lhs => rw [e]
      rw [hinv x' _ hxr0, hx']
    · intro r hr hne
      simp only [GlobalTheory.WeilM.pureA]
      have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : (fun i => (x i).2) ∉ K := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [hsupp x hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    simp only [GlobalTheory.WeilM.pureA]
    have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.WeilAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModule
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.MinkowskiTate

section Lemmas

variable {l : ℕ} {M : Type} [CommGroup M]

theorem lev_nsmul (t : Tate l M) (n m : ℕ) : (n • t).lev m = t.lev m ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; rfl
  | succ n ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem lev_neg (t : Tate l M) (m : ℕ) : (-t).lev m = (t.lev m)⁻¹ := rfl

theorem lev_sub (s t : Tate l M) (m : ℕ) : (s - t).lev m = s.lev m * (t.lev m)⁻¹ := by
  rw [sub_eq_add_neg, Tate.lev_add, lev_neg]

def Dv (k : ℕ) (t : Tate l M) : Prop := ∃ s : Tate l M, t = (l ^ k) • s

theorem dv_zero (k : ℕ) : Dv k (0 : Tate l M) := ⟨0, (smul_zero _).symm⟩

theorem dv_add {k : ℕ} {s t : Tate l M} (hs : Dv k s) (ht : Dv k t) : Dv k (s + t) := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := ht
  exact ⟨a + b, (smul_add _ _ _).symm⟩

theorem dv_neg {k : ℕ} {t : Tate l M} (ht : Dv k t) : Dv k (-t) := by
  obtain ⟨a, rfl⟩ := ht
  exact ⟨-a, (smul_neg _ _).symm⟩

theorem dv_nsmul {k : ℕ} (n : ℕ) {t : Tate l M} (ht : Dv k t) : Dv k (n • t) := by
  obtain ⟨a, rfl⟩ := ht
  exact ⟨n • a, smul_comm _ _ _⟩

theorem dv_sum {k : ℕ} {Ix : Type} (s : Finset Ix) (f : Ix → Tate l M) (h : ∀ i ∈ s, Dv k (f i)) :
    Dv k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Dv k) (fun _ _ => dv_add) (dv_zero k) h

theorem dv_mono {k k' : ℕ} (hk : k ≤ k') {t : Tate l M} (ht : Dv k' t) : Dv k t := by
  obtain ⟨a, rfl⟩ := ht
  refine ⟨l ^ (k' - k) • a, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hk]

theorem eq_zero_of_nsmul {t : Tate l M} (h : l • t = 0) : t = 0 := by
  ext m
  show t.lev m = 1
  calc t.lev m = t.lev (m + 1) ^ l := (Tate.lev_succ t m).symm
    _ = (l • t).lev (m + 1) := (lev_nsmul t l (m + 1)).symm
    _ = 1 := by rw [h]; rfl

theorem eq_zero_of_pow_nsmul (a : ℕ) {z : Tate l M} (h : (l ^ a) • z = 0) : z = 0 := by
  induction a generalizing z with
  | zero => simpa using h
  | succ a ih => exact eq_zero_of_nsmul (ih (by rw [smul_smul, ← pow_succ]; exact h))

theorem pow_nsmul_cancel (a : ℕ) {x y : Tate l M} (h : (l ^ a) • x = (l ^ a) • y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_pow_nsmul a (by rw [smul_sub, h, sub_self]))

theorem dv_of_pow_nsmul {a b : ℕ} {s : Tate l M} (h : Dv (a + b) ((l ^ a) • s)) : Dv b s := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, pow_nsmul_cancel a (by rw [hr, pow_add, smul_smul])⟩

theorem dv_one_of_nsmul {q : ℕ} (hq : Nat.Coprime q l) {s : Tate l M} (h : Dv 1 (q • s)) :
    Dv 1 s := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hq
  refine ⟨a • r + b • s, ?_⟩
  calc s = (a * (q : ℤ) + b * (l : ℤ)) • s := by rw [hab, one_smul]
    _ = a • ((q : ℤ) • s) + b • ((l : ℤ) • s) := by rw [add_smul, mul_smul, mul_smul]
    _ = l ^ 1 • (a • r + b • s) := by
      rw [natCast_zsmul, natCast_zsmul, hr, pow_one, smul_add, smul_comm a l r, smul_comm b l s]

theorem eq_zero_of_dv {t : Tate l M} (h : ∀ k, Dv k t) : t = 0 := by
  ext k
  show t.lev k = 1
  obtain ⟨s, hs⟩ := h k
  rw [hs, lev_nsmul, Tate.lev_pow]

theorem dv_two_of_lev {w : Tate l M} (h : w.lev 2 = 1) : Dv 2 w := by
  refine ⟨Tate.mk (fun n => w.lev (n + 2)) fun n => ⟨?_, ?_⟩, ?_⟩
  · rw [add_comm, Tate.lev_add_pow, h]
  · exact Tate.lev_succ w (n + 2)
  · ext n
    rw [lev_nsmul, Tate.lev_mk, Tate.lev_add_pow]

end Lemmas

end GlobalTheory.MinkowskiTate

namespace GlobalTheory.MinkowskiTate

section Endo

variable {l : ℕ} [Fact l.Prime] {M : Type} [CommGroup M]

theorem dv_pow_sub (k : ℕ) {u : Module.End ℤ_[l] (Tate l M)} (h : ∀ t, Dv k (u t - t)) (n : ℕ) :
    ∀ t, Dv k ((u ^ n) t - t) := by
  induction n with
  | zero => intro t; rw [pow_zero, Module.End.one_apply, sub_self]; exact dv_zero k
  | succ n ih =>
    intro t
    rw [pow_succ', Module.End.mul_apply]
    have e : u ((u ^ n) t) - t = (u ((u ^ n) t) - (u ^ n) t) + ((u ^ n) t - t) := by abel
    rw [e]
    exact dv_add (h _) (ih t)

theorem dv_succ_of_pow_eq_one {q : ℕ} (hq : q.Prime) {v : Module.End ℤ_[l] (Tate l M)}
    (hv : v ^ q = 1) {k : ℕ} (hk : 2 ≤ k) (h : ∀ t, Dv k (v t - t)) (t : Tate l M) :
    Dv (k + 1) (v t - t) := by
  set D := v - 1 with hD
  have hDt : ∀ t, D t = v t - t := fun t => by
    rw [hD, LinearMap.sub_apply, Module.End.one_apply]
  have hmap : ∀ a t, Dv a t → Dv (a + k) (D t) := by
    rintro a _ ⟨s, rfl⟩
    obtain ⟨r, hr⟩ := h s
    refine ⟨r, ?_⟩
    rw [map_nsmul, hDt, hr, pow_add, smul_smul]
  have hpow : ∀ j t, Dv (j * k) ((D ^ j) t) := by
    intro j
    induction j with
    | zero => intro t; exact ⟨t, by rw [pow_zero, Module.End.one_apply, zero_mul, pow_zero, one_smul]⟩
    | succ j ih =>
      intro t
      rw [pow_succ', Module.End.mul_apply, Nat.succ_mul]
      exact hmap _ _ (ih t)
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 + 1 := ⟨q - 2, by have := hq.two_le; omega⟩
  have hvD : v = D + 1 := by rw [hD, sub_add_cancel]
  have key := congrArg (fun f : Module.End ℤ_[l] (Tate l M) => f t) hv
  rw [hvD, (Commute.one_right D).add_pow, Finset.sum_range_succ', Finset.sum_range_succ'] at key
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    one_pow, _root_.mul_one, Module.End.natCast_apply, map_nsmul, pow_zero, Nat.choose_zero_right,
    Nat.choose_one_right, pow_one, Module.End.one_apply, one_smul, zero_add, Nat.cast_one] at key
  have hS : Dv (k + 2) (∑ x ∈ Finset.range (r + 1),
      (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) :=
    dv_sum _ _ fun x _ => dv_nsmul _ (dv_mono (by nlinarith) (hpow (x + 1 + 1) t))
  have hqD : (r + 1 + 1) • D t = -(∑ x ∈ Finset.range (r + 1),
      (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by
    calc (r + 1 + 1) • D t = ((∑ x ∈ Finset.range (r + 1),
          (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) + (r + 1 + 1) • D t + t) - t -
          (∑ x ∈ Finset.range (r + 1), (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by
          abel
      _ = t - t - (∑ x ∈ Finset.range (r + 1),
          (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by rw [key]
      _ = _ := by abel
  have hq2 : Dv (k + 2) ((r + 1 + 1) • D t) := hqD ▸ dv_neg hS
  obtain ⟨s, hs⟩ := h t
  rw [hDt, hs, smul_comm (r + 1 + 1) (l ^ k) s] at hq2
  have h2 : Dv 2 ((r + 1 + 1) • s) := dv_of_pow_nsmul hq2
  have h1 : Dv 1 s := by
    by_cases hql : r + 1 + 1 = l
    · rw [hql] at h2
      exact dv_of_pow_nsmul (a := 1) (b := 1) (by rw [pow_one]; exact h2)
    · exact dv_one_of_nsmul ((Nat.coprime_primes hq Fact.out).2 hql) (dv_mono (by norm_num) h2)
  obtain ⟨r', hr'⟩ := h1
  exact ⟨r', by rw [hs, hr', pow_one, smul_smul, ← pow_succ]⟩

theorem eq_one_of_prime {q : ℕ} (hq : q.Prime) {v : Module.End ℤ_[l] (Tate l M)} (hv : v ^ q = 1)
    (h : ∀ t, Dv 2 (v t - t)) : v = 1 := by
  have hall : ∀ k, 2 ≤ k → ∀ t, Dv k (v t - t) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact h
    | succ k hk ih => exact dv_succ_of_pow_eq_one hq hv hk ih
  refine LinearMap.ext fun t => ?_
  have h0 : v t - t = 0 :=
    eq_zero_of_dv fun k => dv_mono (le_max_left k 2) (hall _ (le_max_right k 2) t)
  rw [Module.End.one_apply]
  exact sub_eq_zero.1 h0

end Endo

end GlobalTheory.MinkowskiTate

theorem GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two : ∀ (l : ℕ) [Fact l.Prime] (M : Type)
    [CommGroup M] (u : Module.End ℤ_[l] (Tate l M)) (E : ℕ), 0 < E → u ^ E = 1 →
    (∀ t, (u t).lev 2 = t.lev 2) → u = 1 := by
  intro l _ M _ u E hE hu h2
  have h : ∀ t, GlobalTheory.MinkowskiTate.Dv 2 (u t - t) := fun t =>
    GlobalTheory.MinkowskiTate.dv_two_of_lev (by rw [GlobalTheory.MinkowskiTate.lev_sub, h2, mul_inv_cancel])
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    rcases Nat.lt_or_ge E 2 with hlt | hge
    · obtain rfl : E = 1 := by omega
      rwa [pow_one] at hu
    · have hq : E.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨E₁, hE₁⟩ := Nat.minFac_dvd E
      have hpos : 0 < E₁ := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hE₁; omega
      have hlt : E₁ < E := by
        have := hq.two_le
        rw [hE₁]
        nlinarith
      have hv : (u ^ E₁) ^ E.minFac = 1 := by rw [← pow_mul, mul_comm, ← hE₁, hu]
      exact ih E₁ hlt hpos (GlobalTheory.MinkowskiTate.eq_one_of_prime hq hv
        (GlobalTheory.MinkowskiTate.dv_pow_sub 2 h E₁))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentEndomorphismQuotientGroupSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_endomorphism_quotient_group_scheme : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ A, IsMonHom f → (∀ h ∈ H, h ≫ f ∈ H) → ∃ f' : A' ⟶ A', IsMonHom f' ∧ ψ ≫ f' = f ≫ ψ := by
  first | exact @GlobalTheory.UPel.HT.Hecke.exists_desc_endo | exact GlobalTheory.UPel.HT.Hecke.exists_desc_endo | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_desc_endo; all_goals assumption)
end

