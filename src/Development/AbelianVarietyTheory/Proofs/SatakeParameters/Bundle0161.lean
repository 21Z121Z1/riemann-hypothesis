import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0154
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeKernelLeOfMatrixLatticeIndexEq
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

theorem ker_le_of_latIdx_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q hU n n' x y hN hidx u hu hyu
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSx
  set Sy := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (y *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSy
  let h : (Fin n' → L) ⧸ intVec L n' → (Fin n' → L) ⧸ intVec L n' := fun c =>
    if hc : ∃ u : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') = c
    then QuotientAddGroup.mk (y *ᵥ (hc.choose : Fin n → L)) else 0
  have key : ∀ w : intVec L n, h (QuotientAddGroup.mk (x *ᵥ (w : Fin n → L))) =
      (QuotientAddGroup.mk (y *ᵥ (w : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') := by
    intro w
    have hc : ∃ u' : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u' : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') =
        QuotientAddGroup.mk (x *ᵥ (w : Fin n → L)) := ⟨w, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he
    rw [QuotientAddGroup.eq]
    have hd := hN ((w : Fin n → L) - (u' : Fin n → L)) (fun i => Subring.sub_mem _ (w.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  have himg : h '' Sx = Sy := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (key w).symm⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨_, ⟨w, rfl⟩, key w⟩
  have hcard : (h '' Sx).ncard = Sx.ncard := by
    rw [himg]
    unfold latIdx at hidx
    rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hidx
    exact hidx
  have hinj : Set.InjOn h Sx := (Set.ncard_image_iff hfin).1 hcard
  let u0 : intVec L n := ⟨u, hu⟩
  have h0 : h (QuotientAddGroup.mk (x *ᵥ ((u0 : intVec L n) : Fin n → L))) = h (QuotientAddGroup.mk (x *ᵥ ((0 : intVec L n) : Fin n → L))) := by
    rw [key, key]
    simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero]
    exact (QuotientAddGroup.eq_zero_iff _).2 hyu
  have h1 := hinj ⟨u0, rfl⟩ ⟨0, rfl⟩ h0
  simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero] at h1
  exact (QuotientAddGroup.eq_zero_iff _).1 h1

end GlobalTheory.Hk3.HoweDuality

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LexSumSplitFirstBlockStrictMono
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem lexSumSplit_strictMono : ∀ (s : ℕ) (t : Fin (s + 1) → ℕ), StrictMono fun c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) => (Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a))) (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c) : Σₗ a, Fin (t a)) := by
  intro s t a b hab
  induction a using Lex.rec with | _ a => ?_
  induction b using Lex.rec with | _ b => ?_
  rcases a with j | x <;> rcases b with j' | x'
  · have h : j < j' := Sum.Lex.inl_lt_inl_iff.mp hab
    simp only [ofLex_toLex, Sum.elim_inl]
    exact Sigma.Lex.right _ _ h
  · simp only [ofLex_toLex, Sum.elim_inl, Sum.elim_inr]
    exact Sigma.Lex.left _ _ (Fin.succ_pos _)
  · exact absurd hab (not_lt_of_gt (Sum.Lex.inl_lt_inr _ _))
  · have h : x < x' := Sum.Lex.inr_lt_inr_iff.mp hab
    simp only [ofLex_toLex, Sum.elim_inr]
    induction x using Lex.rec with | _ x => ?_
    induction x' using Lex.rec with | _ x' => ?_
    rcases x with ⟨i, j⟩
    rcases x' with ⟨i', j'⟩
    change Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨i, j⟩ : Σ a : Fin s, Fin (t a.succ)) ⟨i', j'⟩ at h
    change Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨i.succ, j⟩ : Σ a, Fin (t a)) ⟨i'.succ, j'⟩
    rcases h with ⟨_, _, hi⟩ | ⟨_, _, hj⟩
    · exact Sigma.Lex.left _ _ (Fin.succ_lt_succ_iff.mpr hi)
    · exact Sigma.Lex.right _ _ hj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowTermLeSecondRealPlaceBoundsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_term_le_second_real_place_bounds : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (Xe : ErrX D) (dG : ℕ → ℕ), L.FDef → dG 0 = 0 → (∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam) → WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w), if ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n then FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) - ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
  first | exact @GlobalTheory.TwU.LowTerm.lowS_le | exact GlobalTheory.TwU.LowTerm.lowS_le | (intros; apply GlobalTheory.TwU.LowTerm.lowS_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProduct
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.DetSp

open Polynomial TensorProduct Module

theorem prod_roots_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) : f.charpoly.roots.prod = LinearMap.det f := by
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), ← Matrix.det_eq_prod_roots_charpoly,
    LinearMap.det_toMatrix]

theorem det_map {n m : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (g : Module.End ℂ (Fin m → ℂ)) :
    LinearMap.det (TensorProduct.map f g) = LinearMap.det f ^ m * LinearMap.det g ^ n := by
  classical
  set b := Pi.basisFun ℂ (Fin n)
  set c := Pi.basisFun ℂ (Fin m)
  rw [← LinearMap.det_toMatrix (b.tensorProduct c), TensorProduct.toMatrix_map, Matrix.det_kronecker,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix, Fintype.card_fin, Fintype.card_fin]

theorem det_diagEnd {m : ℕ} (c : Fin m → ℂ) : LinearMap.det (diagEnd c) = ∏ i, c i := by
  classical
  have e : diagEnd c = Matrix.toLin' (Matrix.diagonal c) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [Matrix.mulVec_diagonal]
  rw [e, LinearMap.det_toLin', Matrix.det_diagonal]

theorem sum_centred (m : ℕ) : ∑ i : Fin m, (((i : ℕ) : ℝ) - ((m : ℝ) - 1) / 2) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) - ((m : ℝ) - 1) / 2)), Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ∀ k : ℕ, ∑ i ∈ Finset.range k, (i : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [this]; ring

variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem prod_qPow {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, qPow w (f i) = qPow w (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, qPow_add]

theorem prod_spEig (m : ℕ) : ∏ i, WDRep.spEig w m i = 1 := by
  simp only [WDRep.spEig]
  rw [prod_qPow, sum_centred, qPow_zero]

end GlobalTheory.WeilDeligne.DetSp

namespace GlobalTheory.WeilDeligne

theorem prod_eig_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp h l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  intro E Ω _ _ _ _ _ A w h x l σ
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
      DetSp.prod_roots_charpoly, DetSp.prod_roots_charpoly, DetSp.det_map, DetSp.det_diagEnd,
      Finset.prod_zpow, ← Units.coe_prod, DetSp.prod_spEig, Units.val_one, one_zpow, one_pow, mul_one]

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernelStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLatticeIndex_le_of_integral_kernel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q a b : ℕ) (x y : Matrix (Fin a) (Fin b) L),
    Formalism.UG.IsUnramInv ϖ σ q →
    (∀ u : Fin b → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (Matrix.mulVec x u) i ∈ Formalism.UG.intL L) → ∀ i, (Matrix.mulVec y u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y ≤ GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | exact GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLowerBlockFlag
section
namespace GlobalTheory.LowerBlockFlag

def f0 {k : Type} [Field k] {a s : ℕ} {d : Fin s → ℕ} (e : (i : Fin s) × Fin (d i) ≃ Fin a) (c : Fin s) :
    Submodule k (Fin a → k) where
  carrier := {v | ∀ p : Fin a, c < GlobalTheory.SmGL.blk e p → v p = 0}
  add_mem' {u v} hu hv p hp := by
    rw [Pi.add_apply, hu p hp, hv p hp, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r {v} hv p hp := by
    rw [Pi.smul_apply, hv p hp, smul_zero]

end GlobalTheory.LowerBlockFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSupercuspidalSupportOfTorusJacquetEigenform
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

open GlobalTheory.SmGL.EmptyBlocks GlobalTheory.SmGL.Exponents

namespace GlobalTheory.EigenSupport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jac_mk {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (a : α) × m a ≃ n) (π : Representation ℂ (GL n k) V) (g : Levi k m) (v : V) :
    jac e π g (Submodule.Quotient.mk v) =
      (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • (Submodule.Quotient.mk (π (leviEmb k e g) v) : Jacquet π (unipRad k e)) := rfl

theorem jacB_mk {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (t : n → kˣ) (v : V) :
    jacB π t (Submodule.Quotient.mk v) =
      (((deltaHalf k (fun _ : n => Unit) (leviTorus k n t))⁻¹ : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (π (leviEmb k (points n) (leviTorus k n t)) v) : Jacquet π (unipB k n)) := rfl

theorem leviTorus_eq {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] (t : n → kˣ) :
    leviTorus k n t = torusToLevi k (points n) t := by
  funext j; ext a b
  rw [val_torusToLevi]
  simp [leviTorus, points, Matrix.diagonal]

theorem eq_torusToLevi (n : ℕ) (g : Levi k (fun _ : Fin n => Fin 1)) :
    g = torusToLevi k (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) (fun j => Matrix.GeneralLinearGroup.det (g j)) := by
  funext j; ext a b
  rw [val_torusToLevi]
  fin_cases a; fin_cases b
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

theorem deltaHalf_eq (n : ℕ) (g : Levi k (fun _ : Fin n => Fin 1)) :
    deltaHalf k (fun _ : Fin n => Fin 1) g =
      deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (fun j => Matrix.GeneralLinearGroup.det (g j))) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp_fin (fun _ : Fin n => Fin 1) (fun _ => by simp), modExp_fin (fun _ : Fin n => Unit) (fun _ => by simp)]
  exact congrArg _ (congrFun ((leviTorus k (Fin n)).symm_apply_apply (fun j => Matrix.GeneralLinearGroup.det (g j))) a).symm

theorem inSupport_of_eigenform (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ)
    (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t y, l (jacB π t y) = (torusChar ψ t : ℂ) * l y) (i : Fin n) : InSupport π (ψ i) := by
  let f := Equiv.sigmaUnique (Fin n) fun _ : Fin n => Fin 1
  have hmono : StrictMono (blk f) := fun a b h => by simpa [blk, f] using h
  have h : unipRad k f = unipB k (Fin n) := unipRad_eq k f hmono
  let l' : Jacquet π (unipRad k f) →ₗ[ℂ] ℂ :=
    (twKer π (unipRad k f) 1).liftQ (l ∘ₗ (twKer π (unipB k (Fin n)) 1).mkQ) (by
      rw [h]; intro x hx
      simp [(Submodule.Quotient.mk_eq_zero _).mpr hx])
  have hl' : ∀ v : V, l' (Submodule.Quotient.mk v) = l (Submodule.Quotient.mk v) := fun v => rfl
  let χ : Levi k (fun _ : Fin n => Fin 1) →* ℂˣ := leviChar _ ψ
  have key : ∀ (g : Levi k (fun _ : Fin n => Fin 1)) (v : V),
      l' (jac f π g (Submodule.Quotient.mk v)) = (χ g : ℂ) * l' (Submodule.Quotient.mk v) := by
    intro g v
    set t : Fin n → kˣ := fun j => Matrix.GeneralLinearGroup.det (g j) with ht
    have h1 := hl t (Submodule.Quotient.mk v)
    rw [jacB_mk, map_smul, leviTorus_eq, leviEmb_torusToLevi, ← leviTorus_eq] at h1
    have hEmb : leviEmb k f g = diagT k (Fin n) t := by
      conv_lhs => rw [eq_torusToLevi n g]
      exact leviEmb_torusToLevi k f t
    rw [jac_mk, map_smul, hl', hl', deltaHalf_eq n g, hEmb, ← ht]
    have hc : (χ g : ℂ) = (torusChar ψ t : ℂ) := by
      simp [χ, leviChar_apply, torusChar_apply, t]
    rw [hc, ← h1]
  refine ⟨n, fun _ => 1, f, i, rfl, ℂ, inferInstance, inferInstance, ofChar χ, isIrreducible_ofChar χ, ?_, ?_⟩
  · refine IsSubquotient.of_surjective ⟨l', fun g => ?_⟩ ?_
    · apply Submodule.linearMap_qext
      ext v
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [key, ofChar_apply]
    · obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
        by_contra hc; push_neg at hc; exact hl0 (LinearMap.ext hc)
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      intro c
      refine ⟨(c / l (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, ?_⟩
      show l' _ = c
      rw [map_smul, hl', smul_eq_mul, div_mul_cancel₀ _ hx]
  · intro g y
    rw [ofChar_apply]
    simp [χ, leviChar_apply, Pi.mulSingle_apply, apply_ite, Finset.prod_ite_eq']

end GlobalTheory.EigenSupport

theorem GlobalTheory.EigenSupport.inSupport_of_torus_eigenform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 → (∀ t y, l (jacB π t y) = (torusChar ψ t : ℂ) * l y) → ∀ i, InSupport π (ψ i) := by
  intro k _ _ _ _ n V _ _ π ψ l hl0 hl i
  exact GlobalTheory.EigenSupport.inSupport_of_eigenform n V π ψ l hl0 hl i
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneAddMaximalMatrixIntegralInverse
section
open Matrix

namespace GlobalTheory.Hk3

theorem one_add_maximal_inv_int (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (n : ℕ) (X : Matrix (Fin n) (Fin n) L) (hX : ∀ i j, Valued.v (X i j) < 1) :
    ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧
      ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  classical
  let v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v
  let O := v.valuationSubring
  let Y : Matrix (Fin n) (Fin n) O := fun i j => ⟨X i j, (hX i j).le⟩
  have hY : ∀ i j, IsLocalRing.residue O (Y i j) = 0 := fun i j => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff L v).2 (hX i j)
  have h1 : (IsLocalRing.residue O).mapMatrix (1 + Y) = 1 := by
    rw [map_add, map_one]
    have : (IsLocalRing.residue O).mapMatrix Y = 0 := by
      ext i j; exact hY i j
    rw [this, add_zero]
  have hd : IsUnit (1 + Y).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1, det_one]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨Units.map (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _).toMonoidHom u, ?_, ?_⟩
  · show O.subtype.mapMatrix (u : Matrix (Fin n) (Fin n) O) = _
    rw [hu, map_add, map_one]
    rfl
  · intro i j
    rw [← map_inv]
    exact ((u⁻¹ : (Matrix (Fin n) (Fin n) O)ˣ).1 i j).2

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquiv
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.BlockRename

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n]
  {f : γ' → γ} {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]

omit [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n]
  [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] in

theorem blk_rename {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (j : n) : blk e j = f (blk e₂ j) := by
  obtain ⟨⟨c', x⟩, rfl⟩ := e₂.surjective j
  have h1 : blk e₂ (e₂ ⟨c', x⟩) = c' := blk_apply e₂ c' x
  rw [h1, he, blk_apply]

omit [Fintype γ] [Fintype γ'] [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] in

theorem mem_parab_rename (hf : StrictMono f) {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (g : GL n k) : g ∈ parab k e ↔ g ∈ parab k e₂ := by
  simp only [mem_parab, blk_rename he, hf.lt_iff_lt]

omit [∀ c, DecidableEq (m c)] in

theorem modExp_rename (hf : StrictMono f) (hs : Function.Surjective f) (c' : γ') :
    modExp (fun c' => m (f c')) c' = modExp m (f c') := by
  unfold modExp
  let E := Equiv.ofBijective f ⟨hf.injective, hs⟩
  congr 1
  · rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv E _ _ fun b => if_congr hf.lt_iff_lt.symm rfl rfl
  · rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv E _ _ fun b => if_congr hf.lt_iff_lt.symm rfl rfl

theorem deltaHalf_rename (hf : StrictMono f) (hs : Function.Surjective f) (g : Levi k m) :
    deltaHalf k (fun c' => m (f c')) (fun c' => g (f c')) = deltaHalf k m g := by
  rw [deltaHalf_apply, deltaHalf_apply]
  let E := Equiv.ofBijective f ⟨hf.injective, hs⟩
  exact Fintype.prod_equiv E _ _ fun c' => by rw [modExp_rename hf hs]; rfl

theorem leviProj_rename {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (p : parab k e₂) (q : parab k e) (hpq : (p : GL n k) = q) :
    leviProj k e₂ p = fun c' => leviProj k e q (f c') := by
  funext c'
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, leviProj_apply, he, he, hpq]

def kappa (hf : StrictMono f) (hs : Function.Surjective f) (X : γ → Type) [∀ c, AddCommGroup (X c)]
    [∀ c, Module ℂ (X c)] : (⨂[ℂ] c, X c) ≃ₗ[ℂ] ⨂[ℂ] c', X (f c') :=
  PiTensorProduct.reindex ℂ X (Equiv.ofBijective f ⟨hf.injective, hs⟩).symm

theorem kappa_tprod (hf : StrictMono f) (hs : Function.Surjective f) {X : γ → Type} [∀ c, AddCommGroup (X c)]
    [∀ c, Module ℂ (X c)] (x : ∀ c, X c) :
    kappa hf hs X (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ fun c' => x (f c') := by
  exact PiTensorProduct.reindex_tprod (R := ℂ) (s := X) _ x

theorem piTensor_rename (hf : StrictMono f) (hs : Function.Surjective f) {X : γ → Type}
    [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c))
    (g : Levi k m) (w : ⨂[ℂ] c, X c) :
    piTensor (fun c' => σ (f c')) (fun c' => g (f c')) (kappa hf hs X w) = kappa hf hs X (piTensor σ g w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x => simp only [map_smul, kappa_tprod, piTensor_tprod]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.SmGL.BlockRename

namespace GlobalTheory.SmGL.BlockRename

theorem multiProd_rename : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n] (f : γ' → γ), StrictMono f → Function.Surjective f → ∀ {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (e : (Σ c, m c) ≃ n) (e₂ : (Σ c', m (f c')) ≃ n), (∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) → ∀ {X : γ → Type} [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c)), Nonempty ((multiProd e σ).Equiv (multiProd e₂ fun c' => σ (f c'))) := by
  intro k _ _ _ _ γ γ' n _ _ _ _ _ _ f hf hs m _ _ e e₂ he X _ _ σ
  let κ := kappa hf hs X
  have key : ∀ (p : parab k e₂) (q : parab k e), (p : GL n k) = q → ∀ w,
      ((twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂)) p (κ w) =
        κ (((twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e)) q w) := by
    intro p q hpq w
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, leviProj_rename he p q hpq, twist_apply, twist_apply,
      deltaHalf_rename hf hs, piTensor_rename hf hs]
    exact (map_smul κ _ _).symm
  have hP := mem_parab_rename (k := k) hf he
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear
    (GlobalTheory.SmGL.MultiIrr.indPull
      (σ := (twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂))
      (τ := (twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e))
      (MonoidHom.id _) continuous_id κ.toLinearMap fun p => ⟨⟨p, (hP p).2 p.2⟩, rfl, fun w => key p _ rfl w⟩)
    (GlobalTheory.SmGL.MultiIrr.indPull
      (σ := (twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e))
      (τ := (twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂))
      (MonoidHom.id _) continuous_id κ.symm.toLinearMap fun q => ⟨⟨q, (hP q).1 q.2⟩, rfl, fun w =>
        κ.injective (by
          simp only [LinearEquiv.coe_coe]
          rw [LinearEquiv.apply_symm_apply, ← key ⟨q, (hP q).1 q.2⟩ q rfl, LinearEquiv.apply_symm_apply])⟩) ?_ ?_) fun g => ?_⟩
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => κ.apply_symm_apply (F.1.1 x)))
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => κ.symm_apply_apply (F.1.1 x)))
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => rfl))

end GlobalTheory.SmGL.BlockRename
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductEquivOfNoBlocks
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EmptyProd

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lineEquiv {α n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype n] [DecidableEq n]
    {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) : IndSp e (piTensor σ) ≃ₗ[ℂ] ℂ :=
  haveI : IsEmpty n := ⟨fun x => isEmptyElim (e.symm x).1⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  (LinearEquiv.ofBijective (ev _ 1) ⟨fun f g h =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact h)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩).trans
    (PiTensorProduct.isEmptyEquiv _)

theorem multiProd_equiv_of_isEmpty : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α α' n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype α']
    [LinearOrder α'] [IsEmpty α'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] {m' : α' → Type} [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
    (e : (Σ a, m a) ≃ n) (e' : (Σ a, m' a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] {X' : α' → Type} [∀ a, AddCommGroup (X' a)] [∀ a, Module ℂ (X' a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (σ' : ∀ a, Representation ℂ (GL (m' a) k) (X' a)),
    Nonempty ((multiProd e σ).Equiv (multiProd e' σ')) := by
  intro k _ _ _ _ α α' n _ _ _ _ _ _ _ _ m _ _ m' _ _ e e' X _ _ X' _ _ σ σ'
  haveI : IsEmpty n := ⟨fun x => isEmptyElim (e.symm x).1⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  refine ⟨Representation.Equiv.mk ((lineEquiv e σ).trans (lineEquiv e' σ').symm) fun g => ?_⟩
  rw [Subsingleton.elim g 1, map_one, map_one]
  rfl

end GlobalTheory.EmptyProd
end
end

