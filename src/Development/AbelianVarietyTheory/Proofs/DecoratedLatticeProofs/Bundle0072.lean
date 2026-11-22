import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.RowFormsGood
import Formalism.LocalToGlobal.Divisibility.ClassSumBridge
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStep
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0070
import Formalism.HarderNarasimhan.FinalCor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0043
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmLevelHermitianIntegral
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Col
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem lvl_consequence_one : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K), IsConjAt v0 → ∀ S : CSD K, S.Good 1 → (∀ i j, S.H i j ∈ cmMax K) → (∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) → ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r → S.ActRat r → ∀ (P : Subgroup G) (ψ : P →* Kˣ), (∀ i j, S.lvlH r P ψ i j ∈ cmMax K) ∧ (∀ v : InfinitePlace K, ((S.lvlH r P ψ).map v.embedding).PosDef) ∧ Formalism.HermitianLatticesTheory.dual (hform (S.lvlH r P ψ)) (S.lvlNab r P ψ) ≤ S.lvlNab r P ψ := by
  intro K _ _ _ _ v0 hv0 S hS hH hpos G _ _ r hr hrat P ψ
  have hP := (Formalism.L2.DIV.level_idempotent_spec K v0 hv0 G P ψ).1
  have hE : ∀ i j, S.lvlE r P ψ i j ∈ cmMax K :=
    Formalism.L2.DIV.image_idempotent_rational K S.dim (S.gaMat r (lvlIdem P ψ)) (Formalism.L2.DIV.gaMat_rat S r hrat _ hP.rat)
  have hinj : Function.Injective (S.lvlE r P ψ).mulVec :=
    (Formalism.L2.DIV.image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).1
  refine ⟨fun i j => ?_, fun v => ?_, ?_⟩
  · show ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) i j ∈ cmMax K
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine Subfield.mul_mem _ (Subfield.inv_mem _ (natCast_mem _ _)) (Subfield.sum_mem _ fun k _ => ?_)
    refine Subfield.mul_mem _ ?_ (hE k j)
    rw [Matrix.mul_apply]
    refine Subfield.sum_mem _ fun l _ => Subfield.mul_mem _ ?_ (hH l k)
    rw [Matrix.conjTranspose_apply]
    exact Formalism.L2.DIV.star_mem_cmMax (hE l i)
  · exact Formalism.L2.DIV.cut_posDef S.H (S.lvlE r P ψ) hinj hE (Nat.card P) Nat.card_pos v (hpos v)
  · intro y hy
    have h1 := Formalism.L2.DIV.level_dual_lattice_le K v0 hv0 S 1 hS (hpos v0) G r hr P ψ y hy
    rw [Nat.cast_one, one_smul] at h1
    show (S.lvlE r P ψ).mulVec y ∈ S.nabLat
    have h2 : (S.lvlE r P ψ).mulVec y ∈ S.delLat := h1
    have hle : S.delLat ≤ S.nabLat := by
      intro x hx
      simp only [CSD.delLat, CSD.nabLat, Formalism.DivisionValues.valLatF, Submodule.mem_comap, Submodule.mem_pi,
        Set.mem_univ, true_implies] at hx ⊢
      exact fun c => hS.del_le c (hx c)
    exact hle h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvGSDOkOfEqOne
section
noncomputable section

namespace GlobalTheory.CoreHt

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

theorem evGSD_ok_of_eq_one : ∀ (X : Fields) [IsTotallyComplex X.K] (hX : X.Ok) (Pr : Primes X) (R : Ranks)
    (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word), Pr.Ok → mu = 1 → (evGSD W Ch sel mu P u).Ok := by
  intro X _ hX Pr R W Ch sel Sg mu P u hPr hmu
  subst hmu
  exact GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u

end GlobalTheory.CoreHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvertibleFamilyEvalSpan
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KJInf

def evalLin {ι : Type} {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₗ[ℂ] ℂ where
  toFun := evalAt y
  map_add' F G := by simp [evalAt]
  map_smul' c F := by simp [evalAt, MvPolynomial.smul_eval]

theorem evalLin_apply {ι : Type} {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalLin y F = evalAt y F := rfl

theorem exists_evalAt_span (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ)
    (W : Type) [AddCommGroup W] [Module ℂ W] (T : PY ι a →ₗ[ℂ] W) :
    ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → W),
      (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, T F = ∑ j, evalAt (y j) F • P j := by
  classical
  set V := Vn lam n with hV
  haveI : FiniteDimensional ℂ V := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam n).1
  have hsep : ∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0 :=
    (GlobalTheory.T.fockSubstitution_identities ι a a le_rfl).2.2.2.2.2.2.1
  let S : Set (Module.Dual ℂ V) :=
    {φ | ∃ y : ι → Matrix (Fin a) (Fin a) ℂ, IsInv y ∧ φ = (evalLin y).comp V.subtype}
  obtain ⟨f, hfS, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ S
  choose y hy hfy using hfS
  let Φ := LinearMap.pi f
  have hinj : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro F hF
    have h0 : ∀ φ ∈ Submodule.span ℂ S, φ F = 0 := by
      intro φ hφ
      rw [← hspan] at hφ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact congrFun hF j
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c x _ hx => simp [hx]
    have hF0 : (F : PY ι a) = 0 := by
      apply hsep
      intro z hz
      have := h0 ((evalLin z).comp V.subtype) (Submodule.subset_span ⟨z, hz, rfl⟩)
      simpa [evalLin_apply] using this
    exact Subtype.ext hF0
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Φ hinj
  refine ⟨_, y, fun j => T (L (Pi.single j 1) : PY ι a), hy, ?_⟩
  intro F hF
  have hΦ : Φ ⟨F, hF⟩ = ∑ j, evalAt (y j) F • (Pi.single j 1 : Fin _ → ℂ) := by
    ext i
    simp only [Φ, LinearMap.pi_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hfy i]
    rfl
  have key : (⟨F, hF⟩ : V) = L (Φ ⟨F, hF⟩) := by
    rw [← LinearMap.comp_apply, hL]; rfl
  calc T F = T ((⟨F, hF⟩ : V) : PY ι a) := rfl
    _ = T ((L (Φ ⟨F, hF⟩) : V) : PY ι a) := by rw [← key]
    _ = ∑ j, evalAt (y j) F • T (L (Pi.single j 1) : PY ι a) := by
      rw [hΦ, map_sum]
      simp [map_smul, Submodule.coe_sum, Submodule.coe_smul]

end GlobalTheory.KJInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianSelfDualMaxSlopeStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_self_dual_max_slope : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K), IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), IsRatHerm K0 H X → ∀ M : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K M → Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → 0 < n → (Formalism.L2.DIV.toHLat X M).muMaxDual ≤ 0 := by
  first | exact @GlobalTheory.IntegralDualSlope.muMaxDual_nonpos | exact GlobalTheory.IntegralDualSlope.muMaxDual_nonpos | (intros; apply GlobalTheory.IntegralDualSlope.muMaxDual_nonpos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweDualityUnitarySubstitutionSpanUnit
section
noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf GlobalTheory.GLDuality
open scoped Matrix Kronecker

namespace GlobalTheory.HoweOne

def ren (a b : ℕ) : FP Unit a b →ₐ[ℂ] MvPolynomial (Fin b × Fin a) ℂ :=
  rename Prod.snd

theorem ren_X {a b : ℕ} (v : Unit × Fin b × Fin a) : ren a b (X v) = X v.2 := by
  simp [ren]

theorem ren_injective (a b : ℕ) : Function.Injective (ren a b) :=
  rename_injective _ fun u v h => Prod.ext (Subsingleton.elim _ _) h

theorem matRep_ren {a b : ℕ} (g : GL (Fin a) ℂ) (h : GL (Fin b) ℂ) (P : FP Unit a b) :
    matRep a b (g, h) (ren a b P) =
      ren a b (mvZ (fun _ => (g : Matrix (Fin a) (Fin a) ℂ)ᵀ) (fun _ => (h : Matrix (Fin b) (Fin b) ℂ)) P) := by
  rw [matRep_apply]
  have e : (Formalism.GradedWeylDivisibility.sub ((h : Matrix (Fin b) (Fin b) ℂ) ⊗ₖ (g : Matrix (Fin a) (Fin a) ℂ))ᵀ).comp (ren a b) =
      (ren a b).comp
        (mvZ (fun _ => (g : Matrix (Fin a) (Fin a) ℂ)ᵀ) (fun _ => (h : Matrix (Fin b) (Fin b) ℂ))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨u, i, j⟩
    rw [AlgHom.comp_apply, AlgHom.comp_apply, ren_X, ← matRep_apply, matRep_X]
    simp [mvZ, map_sum, ren_X, Matrix.transpose_apply]
  exact congrArg (fun φ => φ P) e

theorem subY_one_injective {a b : ℕ} (hab : a ≤ b) :
    Function.Injective (subY (ι := Unit) hab (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ))) := by
  have e : subY (ι := Unit) hab (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) =
      rename fun v : Unit × Fin a × Fin a => (v.1, Fin.castLE hab v.2.2, v.2.1) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨u, i, j⟩
    simp [subY, Matrix.one_apply, apply_ite C]
  rw [e]
  apply rename_injective
  rintro ⟨u, i, j⟩ ⟨u', i', j'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, h2, rfl⟩ := h
  rw [Fin.castLE_injective hab h2]

end GlobalTheory.HoweOne

namespace GlobalTheory.HoweOne

open GlobalTheory.Branching

theorem vn_stable {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) (g : Unit → Matrix (Fin a) (Fin a) ℂ) :
    ∀ F ∈ Vn lam n, lft g F ∈ Vn lam n := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable Unit a lam n).2 g

def vnMap {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) (g : Unit → Matrix (Fin a) (Fin a) ℂ) :
    Vn lam n →ₗ[ℂ] Vn lam n :=
  LinearMap.restrict (p := Vn lam n) (q := Vn lam n) (lft g).toLinearMap (vn_stable lam n g)

theorem vnMap_apply {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) (g : Unit → Matrix (Fin a) (Fin a) ℂ)
    (F : Vn lam n) : (vnMap lam n g F : PY Unit a) = lft g F := rfl

theorem transpose_uni {a : ℕ} (k : Matrix.unitaryGroup (Fin a) ℂ) :
    (k : Matrix (Fin a) (Fin a) ℂ)ᵀ ∈ Matrix.unitaryGroup (Fin a) ℂ :=
  Matrix.transpose_mem_unitaryGroup_iff.2 k.2

def vnRep {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) :
    Representation ℂ (Matrix.unitaryGroup (Fin a) ℂ) (Vn lam n) where
  toFun k := vnMap lam n (fun _ => (k : Matrix (Fin a) (Fin a) ℂ)ᵀ)
  map_one' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    rw [vnMap_apply, Module.End.one_apply]
    have : (fun _ : Unit => ((1 : Matrix.unitaryGroup (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) = fun _ => 1 := by
      exact funext fun _ => Matrix.transpose_one
    rw [this, (GlobalTheory.T.fockSubstitution_identities Unit a a le_rfl).2.2.2.2.1]
  map_mul' k k' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    rw [Module.End.mul_apply, vnMap_apply, vnMap_apply, vnMap_apply, (GlobalTheory.T.fockSubstitution_identities Unit a a le_rfl).2.2.2.1]
    congr 2
    refine funext fun _ => ?_
    first | exact (Matrix.transpose_mul _ _).symm | exact Matrix.transpose_mul _ _

theorem vnRep_apply {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) (k : Matrix.unitaryGroup (Fin a) ℂ)
    (F : Vn lam n) : (vnRep lam n k F : PY Unit a) = lft (fun _ => (k : Matrix (Fin a) (Fin a) ℂ)ᵀ) F := rfl

theorem vnRep_irreducible {a : ℕ} (ha : 0 < a) (lam : Unit → DomWeight a) (n : Unit → ℕ) :
    (vnRep lam n).IsIrreducible := by
  obtain ⟨hne, hirr⟩ := GlobalTheory.T.weylDeterminantTwistTensor_unitIndex_irreducible_unitary a ha lam n
  obtain ⟨F₀, hF₀, hF₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have e' := congrArg Subrepresentation.toSubmodule e
    have : (⟨F₀, hF₀⟩ : Vn lam n) ∈ (⊤ : Subrepresentation (vnRep lam n)).toSubmodule := Submodule.mem_top
    rw [← e'] at this
    exact hF₀0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 this))
  · let U : Submodule ℂ (PY Unit a) := S.toSubmodule.map (Vn lam n).subtype
    have hU : U ≤ Vn lam n := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hst : ∀ k, IsUni k → ∀ F ∈ U, lft k F ∈ U := by
      rintro k hk _ ⟨x, hx, rfl⟩
      let u : Matrix.unitaryGroup (Fin a) ℂ := ⟨(k ())ᵀ, Matrix.transpose_mem_unitaryGroup_iff.2 (hk ())⟩
      refine ⟨vnRep lam n u x, S.apply_mem_toSubmodule u hx, ?_⟩
      have hk' : (fun _ : Unit => (u : Matrix (Fin a) (Fin a) ℂ)ᵀ) = k := by
        funext t; simp [u]
      simp only [Submodule.subtype_apply, vnRep_apply, hk']
    rcases hirr U hU hst with h | h
    · left
      refine Subrepresentation.ext ((Submodule.eq_bot_iff _).2 fun x hx => ?_)
      have : (x : PY Unit a) ∈ U := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    · right
      refine Subrepresentation.ext (Submodule.eq_top_iff'.2 fun x => ?_)
      have : (x : PY Unit a) ∈ U := by rw [h]; exact x.2
      obtain ⟨y, hy, hyx⟩ := this
      rwa [Subtype.ext hyx] at hy

theorem equiv_unitary_gl {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nonempty ((Representation.directSum fun j : Part (min a b) =>
      Representation.tprod ((smallRep (unitaryIncl a) (pad a j)).comp
          (MonoidHom.fst (Matrix.unitaryGroup (Fin a) ℂ) (GL (Fin b) ℂ)))
        ((smallRep (MonoidHom.id (GL (Fin b) ℂ)) (pad b j)).comp
          (MonoidHom.snd (Matrix.unitaryGroup (Fin a) ℂ) (GL (Fin b) ℂ)))).Equiv
      (polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)))) := by
  obtain ⟨⟨e⟩, -, -⟩ := (GlobalTheory.Published.glHoweDuality_holds a b ha hb).1
  exact ⟨Representation.Equiv.mk e.toLinearEquiv fun u => e.isIntertwining' (unitaryIncl a u.1, u.2)⟩

end GlobalTheory.HoweOne

namespace GlobalTheory.HoweOne

open GlobalTheory.Branching

def subMap {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ)
    (y' : Unit → Matrix (Fin b) (Fin b) ℂ) : Vn lam n →ₗ[ℂ] MvPolynomial (Fin b × Fin a) ℂ :=
  (ren a b).toLinearMap ∘ₗ (subY hab y').toLinearMap ∘ₗ (Vn lam n).subtype

theorem subMap_apply {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ)
    (y' : Unit → Matrix (Fin b) (Fin b) ℂ) (F : Vn lam n) :
    subMap hab lam n y' F = ren a b (subY hab y' F) := rfl

def subSet {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ) :
    Set (Vn lam n →ₗ[ℂ] MvPolynomial (Fin b × Fin a) ℂ) :=
  {T | ∃ y', IsInv y' ∧ T = subMap hab lam n y'}

theorem polyRep_apply {a b : ℕ} (k : Matrix.unitaryGroup (Fin a) ℂ) (h : GL (Fin b) ℂ) (P : FP Unit a b) :
    polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, h) (ren a b P) =
      ren a b (mvZ (fun _ => (k : Matrix (Fin a) (Fin a) ℂ)ᵀ) (fun _ => (h : Matrix (Fin b) (Fin b) ℂ)) P) :=
  matRep_ren (unitaryIncl a k) h P

theorem subMap_intertwines {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ)
    (y' : Unit → Matrix (Fin b) (Fin b) ℂ) (k : Matrix.unitaryGroup (Fin a) ℂ) (F : Vn lam n) :
    subMap hab lam n y' (vnRep lam n k F) =
      polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, 1) (subMap hab lam n y' F) := by
  rw [subMap_apply, subMap_apply, polyRep_apply, (GlobalTheory.T.fockSubstitution_identities Unit a b hab).1, vnRep_apply]
  simp only [Units.val_one, one_mul]

theorem comp_subMap {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ)
    (y' : Unit → Matrix (Fin b) (Fin b) ℂ) (h : GL (Fin b) ℂ) :
    polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (1, h) ∘ₗ subMap hab lam n y' =
      subMap hab lam n (fun τ => (h : Matrix (Fin b) (Fin b) ℂ) * y' τ) := by
  refine LinearMap.ext fun F => ?_
  rw [LinearMap.comp_apply, subMap_apply, subMap_apply, polyRep_apply, (GlobalTheory.T.fockSubstitution_identities Unit a b hab).1]
  have : (fun _ : Unit => ((1 : Matrix.unitaryGroup (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) = fun _ => 1 :=
    funext fun _ => Matrix.transpose_one
  rw [this, (GlobalTheory.T.fockSubstitution_identities Unit a a le_rfl).2.2.2.2.1]

theorem howeSpan_unit : HoweSpan Unit := by
  intro a b hab ha lam n Q hQ
  haveI : FiniteDimensional ℂ (Vn lam n) := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable Unit a lam n).1
  have hb : 1 ≤ b := le_trans ha hab
  let S := Submodule.span ℂ (subSet hab lam n)
  have h1 : ∀ T ∈ S, ∀ k F, T (vnRep lam n k F) =
      polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, 1) (T F) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨y', -, rfl⟩ := hT
      exact subMap_intertwines hab lam n y'
    | zero => intro k F; simp
    | add T T' _ _ hT hT' => intro k F; simp [hT k F, hT' k F]
    | smul c T _ hT => intro k F; simp [hT k F]
  have h2 : ∀ T ∈ S, ∀ h, polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (1, h) ∘ₗ T ∈ S := by
    intro T hT h
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨y', hy', rfl⟩ := hT
      rw [comp_subMap]
      refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
      rw [Matrix.det_mul]
      exact (Matrix.isUnits_det_units h).mul (hy' τ)
    | zero => simp
    | add T T' _ _ hT hT' => rw [LinearMap.comp_add]; exact S.add_mem hT hT'
    | smul c T _ hT => rw [LinearMap.comp_smul]; exact S.smul_mem c hT
  have h3 : S ≠ ⊥ := by
    obtain ⟨F₀, hF₀, hF₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.T.weylDeterminantTwistTensor_unitIndex_irreducible_unitary a ha lam n).1
    have hmem : subMap hab lam n (fun _ => 1) ∈ S :=
      Submodule.subset_span ⟨_, fun _ => by simp, rfl⟩
    intro hS
    rw [hS, Submodule.mem_bot] at hmem
    have := LinearMap.congr_fun hmem ⟨F₀, hF₀⟩
    rw [subMap_apply, LinearMap.zero_apply] at this
    exact hF₀0 (subY_one_injective hab ((map_eq_zero_iff _ (ren_injective a b)).1 this |>.trans
      (map_zero _).symm))
  let Q' : Vn lam n →ₗ[ℂ] MvPolynomial (Fin b × Fin a) ℂ := (ren a b).toLinearMap ∘ₗ Q ∘ₗ (Vn lam n).subtype
  have hQ' : ∀ k F, Q' (vnRep lam n k F) = polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, 1) (Q' F) := by
    intro k F
    simp only [Q', LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [vnRep_apply, polyRep_apply, hQ _ (fun _ => transpose_uni k) F F.2]
    rfl
  have key := GlobalTheory.T.equivariantHom_multiplicityFree_irreducible (Matrix.unitaryGroup (Fin a) ℂ) (GL (Fin b) ℂ) (Part (min a b))
    (fun j => nablaSq ℂ a (pad a j)) (fun j => nablaSq ℂ b (pad b j))
    (fun j => smallRep (unitaryIncl a) (pad a j)) (fun j => smallRep (MonoidHom.id (GL (Fin b) ℂ)) (pad b j))
    (irreducibleDistinct_unitary (min_le_left a b)).1 (irreducibleDistinct_gl (min_le_right a b)).1
    (irreducibleDistinct_unitary (min_le_left a b)).2
    (MvPolynomial (Fin b × Fin a) ℂ) (polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)))
    (equiv_unitary_gl ha hb) (Vn lam n) (vnRep lam n) (vnRep_irreducible ha lam n) S h1 h2 h3 Q' hQ'
  obtain ⟨m, c, T, hT⟩ := Submodule.mem_span_set'.1 key
  choose y' hy' hyT using fun i => (T i).2
  refine ⟨m, y', c, hy', fun F hF => ren_injective a b ?_⟩
  have := LinearMap.congr_fun hT ⟨F, hF⟩
  rw [LinearMap.sum_apply] at this
  simp only [LinearMap.smul_apply, hyT, subMap_apply] at this
  simp only [map_sum, map_smul]
  exact this.symm

end GlobalTheory.HoweOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Col2.PtUniq

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem mem_iff_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) (v : Sp E n) :
    v ∈ N ↔ (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) N := by
  have h1 := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.2 hN.fg) hN.span_eq_top
  conv_lhs => rw [← h1]
  have e1 : ∀ (x : GL (Fin n) (AfE F E)) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E),
      v ∈ Formalism.UG.CS.globLat x Λ ↔ Matrix.mulVec ((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))
        (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
    fun _ _ _ => Iff.rfl
  rw [e1, inv_one, Units.val_one, Matrix.one_mulVec]

theorem isPtOf_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (g : GL (Fin n) (Formalism.L2.DIV.AfE F E))
    (p p' : Formalism.L2.Col.DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g p → GlobalTheory.Mem.Col2.IsPtOf hc g p' → p = p' := by
  intro F E _ _ _ _ _ _ hc n ST SG Q g p p' h h'
  have hN : p.deco.1.N = p'.deco.1.N := by
    ext v
    rw [mem_iff_hatL (F := F) p.deco.2.lat, mem_iff_hatL (F := F) p'.deco.2.lat, h.lat, h'.lat]
  have hd : p.deco = p'.deco := by
    apply Subtype.ext
    refine Deco.Ok.ext_on p.deco.2 p'.deco.2 hN (fun P x hx => ?_) (fun w x hx => ?_)
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hx0 : x = 0 := Subsingleton.elim _ _
        subst hx0
        have a := p.deco.2.f_smul P 0 0 (zero_mem _)
        have b := p'.deco.2.f_smul P 0 0 (zero_mem _)
        rw [zero_smul, map_zero, zero_mul] at a b
        rw [a, b]
      · exact HasRes.unique (h.f P x hx ⟨n - 1, by omega⟩ (by simp; omega))
          (h'.f P x (hN ▸ hx) ⟨n - 1, by omega⟩ (by simp; omega))
    · funext i
      exact HasRes.unique (h.be w x hx i) (h'.be w x (hN ▸ hx) i)
  have hfr : ∀ P : Q, p.fr P = p'.fr P := by
    intro P
    refine LinearEquiv.toLinearMap_injective (Module.Basis.ext (Pi.basisFun E (Fin n)) fun j => ?_)
    funext i
    have e := (h.fr P i j).symm.trans (h'.fr P i j)
    simpa using (algebraMap E (P.1.adicCompletion E)).injective e
  apply Subtype.ext
  exact Prod.ext hd (funext hfr)

end GlobalTheory.Mem.Col2.PtUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricBiTransformingLowerUnipotentDiagValue
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

namespace GlobalTheory.LowerHeckeSupp

theorem lowU_add {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (a b : Matrix D A k) :
    lowU (a + b) = lowU a * lowU b := by
  ext1
  rw [Units.val_mul, val_lowU, val_lowU, val_lowU, fromBlocks_multiply]
  simp [add_comm]

theorem biType_lowU_emb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ φ : GL (A ⊕ D) k → ℂ, IsBiType ξ φ → ∀ (ν : Matrix D A k) (y : GL D k), φ (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) = if ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧ ν = ν₁ + y.1 * ν₂ then φ (emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) else 0 := by
  intro k _ _ _ _ A D _ _ _ _ ξ hT hU φ hφ ν y
  split_ifs with h
  · obtain ⟨ν₁, ν₂, h₁, h₂, rfl⟩ := h
    have hd : ∀ μ : Matrix D A k, ((1 : kˣ) : k) = ((lowU μ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det := by
      intro μ; simp [val_lowU]
    rw [lowU_add, mul_assoc, ← emb_mul_lowU]
    rw [(hφ _ (lowU_mem h₁) 1 (hd ν₁) _).1, (hφ _ (lowU_mem h₂) 1 (hd ν₂) _).2]
    simp
  · by_contra hne
    obtain ⟨x, z, j, hj, j', hj', he⟩ := GlobalTheory.ParHeckeSupp.support_levi k A D ξ hT hU φ hφ _ hne
    have hv : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)).1 = fromBlocks 1 0 ν y.1 := by
      rw [Units.val_mul, val_lowU, val_emb_one, fromBlocks_multiply]; simp
    exact h (GlobalTheory.ParHeckeCap.lowerUni_mem_cap k A D _ ν y hv ⟨x, z, j, hj, j', hj', he⟩)

end GlobalTheory.LowerHeckeSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumCompletionEqColumnTestFunctionStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepDatum_completion_eq_columnTestFunction : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → TopAgree Ch sel mu cst σ₀ P ι S ν := by
  first | exact @GlobalTheory.SymBridge.LastStepProof.topAgree | exact GlobalTheory.SymBridge.LastStepProof.topAgree | (intros; apply GlobalTheory.SymBridge.LastStepProof.topAgree <;> assumption)
end

