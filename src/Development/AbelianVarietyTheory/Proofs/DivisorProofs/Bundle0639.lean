import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientNormSquareData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunIffRowSlopeBound
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.RowSlopeCompare

open Formalism.DivisionValues Formalism.L2.Indef GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Same

variable {Bs : DefBase K} {Df : DefSide Bs} {κ : Bs.Tup → Type} [∀ t, Fintype (κ t)]
  [∀ t, DecidableEq (κ t)] {τ : Type} {m : ℕ}

structure Same (S : IndefData Df) (D : RowData K Bs.Tup κ τ (Fin S.D) Bs.Ix m)
    (e : ∀ t, (Fin (Df.nV t) → K) →ₗ[K] (κ t → K)) (σ : Fin m ≃ Bs.J) : Prop where

  ref : D.t₀ = Bs.μ0

  tup : D.tup = S.μ

  inj : ∀ t, Function.Injective (e t)

  good : ∀ t, LinearMap.range (e t) = D.V₀ t

  lat : ∀ t, (Df.Mt t).map ((e t).restrictScalars (𝓞 K)) = D.M t ⊓ (D.V₀ t).restrictScalars (𝓞 K)

  iota : ∀ t F, D.psi.mulVec ((S.ι t).mulVec ((Df.Pq t).mulVec F)) =
    (((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (e t F)

  part : D.part = S.Ep

  lam : ∀ p j c, D.lam p j c = S.lam (σ j) Bs.μ0 c p

  kap : D.kap = S.κ

  frame : D.XE = S.XE

variable {S : IndefData Df} {D : RowData K Bs.Tup κ τ (Fin S.D) Bs.Ix m}
  {e : ∀ t, (Fin (Df.nV t) → K) →ₗ[K] (κ t → K)} {σ : Fin m ≃ Bs.J}

end Same

theorem quotNormSq_eq [IsTotallyComplex K] {n d D : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding)
    (P : Matrix (Fin d) (Fin n) K) (hP : Function.Surjective P.mulVec)
    (XQ : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hQ : IsQuotMetric P H XQ)
    (ι : Matrix (Fin D) (Fin d) K) (hι : Function.Injective ι.mulVec) (v : InfinitePlace K) (y : Fin d → K) :
    quotNormSq X0 ⊤ (ι * P) v (ι.mulVec y) = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) XQ v y ^ 2 := by
  obtain ⟨hle, hrep⟩ := quotMetricRep K n d H X0 hX P hP XQ hQ v
  have hmap : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) K) (x : Fin b → K),
      (fun i => v.embedding (A.mulVec x i)) = (A.map v.embedding).mulVec fun i => v.embedding (x i) := by
    intro a b A x
    funext i
    simp [Matrix.mulVec, dotProduct]
  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin n) (Fin d) K, P * R = 1 := by
    obtain ⟨g, hg⟩ := P.mulVecLin.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  have hlow : ∀ s ∈ {s : ℝ | ∃ F ∈ (⊤ : Submodule K (Fin n → K)), (ι * P).mulVec F = ι.mulVec y ∧
      s = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2},
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) XQ v y ^ 2 ≤ s := by
    rintro _ ⟨F, -, hF, rfl⟩
    rw [← Matrix.mulVec_mulVec] at hF
    have hF' := hι hF
    refine pow_le_pow_left₀ (Formalism.BasicNotions.normAt_nonneg _ _ _ _) ?_ 2
    rw [← (fnormRat K d XQ v y y).1, ← (fnormRat K n X0 v F F).1, ← hF', hmap]
    exact hle _
  have hmem : ∀ G : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v
      (G + R.mulVec (y - P.mulVec G)) ^ 2 ∈ {s : ℝ | ∃ F ∈ (⊤ : Submodule K (Fin n → K)),
      (ι * P).mulVec F = ι.mulVec y ∧ s = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2} := by
    intro G
    refine ⟨_, trivial, ?_, rfl⟩
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec (M := P), hR, Matrix.one_mulVec,
      add_sub_cancel]
  refine le_antisymm ?_ (le_csInf ⟨_, hmem 0⟩ hlow)
  obtain ⟨z, hz, hn, -⟩ := hrep fun i => v.embedding (y i)
  let f : (Fin n → ℂ) → ℝ := fun u => fnorm (X0 v) (u + (R.map v.embedding).mulVec
    ((fun i => v.embedding (y i)) - (P.map v.embedding).mulVec u)) ^ 2
  have hf : Continuous f := by
    unfold f fnorm Formalism.HermitianLatticesTheory.cnorm
    fun_prop
  have hd : DenseRange (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => Formalism.BasicNotions.denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have key : quotNormSq X0 ⊤ (ι * P) v (ι.mulVec y) ≤ f z := by
    refine hd.induction_on (p := fun u => quotNormSq X0 ⊤ (ι * P) v (ι.mulVec y) ≤ f u) z
      (isClosed_le continuous_const hf) fun G => ?_
    refine (csInf_le ⟨_, hlow⟩ (hmem G)).trans (le_of_eq ?_)
    rw [← (fnormRat K n X0 v _ 0).1]
    unfold f
    congr 2
    have h1 := hmap R (y - P.mulVec G)
    have h2 := hmap P G
    funext i
    have h3 : (fun i => v.embedding ((y - P.mulVec G) i)) = (fun i => v.embedding (y i)) -
        (P.map v.embedding).mulVec (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)) G) := by
      funext k
      simp only [Pi.sub_apply, map_sub, congrFun h2 k]
      rfl
    rw [Pi.add_apply, map_add, congrFun h1 i, h3]
    rfl
  refine key.trans (le_of_eq ?_)
  unfold f
  rw [hz, sub_self, Matrix.mulVec_zero, add_zero, hn, (fnormRat K d XQ v y y).1]

def PartsOrth {Bs : DefBase K} (Df : DefSide Bs) : Prop :=
  ∀ v p p', p ≠ p' → ∀ x ∈ Df.Qp Bs.μ0 p, ∀ y ∈ Df.Qp Bs.μ0 p',
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) v x y = 0

section Forward

variable [IsTotallyComplex K] {Bs : DefBase K} {Df : DefSide Bs}

def toRowData (S : IndefRows Df) (wf : Df.WF) (ho : PartsOrth Df) :
    RowData K Bs.Tup (fun t => Fin (Df.nV t)) (Fin S.D) (Fin S.D) Bs.Ix (Fintype.card Bs.J) where
  t₀ := Bs.μ0
  tup := S.μ
  tup_finite := twisted_finite S
  M := Df.Mt
  M_lattice := wf.Mt_lat
  V₀ _ := ⊤
  v t := S.ι t * Df.Pq t
  r _ := 1
  r_ref := rfl
  X₀ := Formalism.L2.DIV.stdFrame (Df.HV Bs.μ0)
  X₀_unit p := (Formalism.L2.DIV.frameOfSpec _ _ (wf.HV_pos _ p)).1
  psi := 1
  psi_injective := by simpa using Function.injective_id
  psi_range := by
    rw [Matrix.mulVecLin_one, LinearMap.range_id, Submodule.map_top, eq_comm, LinearMap.range_eq_top,
      Matrix.mulVecLin_mul]
    exact (S.l1c.1 _).2.comp (wf.Pq_surj _)
  part := S.Ep
  part_span := (S.Ep_decomp wf).2
  lam p j c := S.lam ((Fintype.equivFin Bs.J).symm j) Bs.μ0 c p
  lam_pos p j c := S.l1c.2.2.2.1 _ _ _ _
  kap := S.κ
  kap_pos := S.l1c.2.2.1
  XE := S.XE
  XE_unit := S.frames.1
  XE_norm p c x hx := by
    obtain ⟨y, rfl⟩ := (S.l1c.1 Bs.μ0).2 x
    rw [Matrix.one_mulVec, quotNormSq_eq (Df.HV Bs.μ0) (Formalism.L2.DIV.stdFrame (Df.HV Bs.μ0))
      (fun v => Formalism.L2.DIV.frameOfSpec _ _ (wf.HV_pos _ v)) _ (wf.Pq_surj _) _ (wf.XQ_quot _) _ (S.l1c.1 _).1,
      Formalism.BasicNotions.normAt_sq_eq_majAt, Formalism.BasicNotions.normAt_sq_eq_majAt,
      S.l1c.2.2.2.2.1 Bs.μ0 p (Or.inl rfl) c y hx y, Complex.re_ofReal_mul,
      Equiv.prod_comp (Fintype.equivFin Bs.J).symm (fun j => S.lam j Bs.μ0 c p)]
  XE_orth p c c' hc x hx y hy := by
    obtain ⟨x, rfl⟩ := (S.l1c.1 Bs.μ0).2 x
    obtain ⟨y, rfl⟩ := (S.l1c.1 Bs.μ0).2 y
    rw [S.l1c.2.2.2.2.1 Bs.μ0 p (Or.inl rfl) c x hx y,
      ho p c c' hc x (S.Qpart_base c ▸ hx) y (S.Qpart_base c' ▸ hy), mul_zero]

end Forward

section Backward

variable {T : Type} {κ : T → Type} [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] {τ C : Type} [Fintype C]
  {n m : ℕ} (D : RowData K T κ τ (Fin n) C m) (v0 : InfinitePlace K)

def OneForm : Prop := ∀ t, (D.V₀ t).map (D.v t).mulVecLin = LinearMap.range D.psi.mulVecLin

abbrev baseOf : DefBase K where
  K0 := cmMax K
  v0 := v0
  Tup := T
  μ0 := D.t₀
  Ix := C
  fIx := inferInstance
  J := Fin m
  fJ := inferInstance

def coords (t : T) : (Fin (finrank K (D.V₀ t)) → K) →ₗ[K] (κ t → K) :=
  (D.V₀ t).subtype ∘ₗ (Module.finBasis K (D.V₀ t)).equivFun.symm.toLinearMap

theorem coords_range (t : T) : LinearMap.range (coords D t) = D.V₀ t := by
  rw [coords, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

theorem exists_proj (h : OneForm D) (t : T) : ∃ P : Matrix (Fin n) (Fin (finrank K (D.V₀ t))) K,
    Function.Surjective P.mulVec ∧ ∀ F, D.psi.mulVec (P.mulVec F) =
      (((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (coords D t F) := by
  obtain ⟨g, hg⟩ := D.psi.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 D.psi_injective)
  have hg' : ∀ x, g (D.psi.mulVec x) = x := fun x => LinearMap.congr_fun hg x
  have hs : ∀ F, D.psi.mulVec ((LinearMap.toMatrix'
      (g ∘ₗ ((((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVecLin) ∘ₗ coords D t)).mulVec F) =
      (((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (coords D t F) := by
    intro F
    have hF : (((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (coords D t F) ∈ LinearMap.range D.psi.mulVecLin := by
      rw [← h t]
      exact Submodule.smul_mem _ _ ⟨_, (coords_range D t).le (LinearMap.mem_range_self _ F), rfl⟩
    obtain ⟨x, hx⟩ := hF
    rw [LinearMap.toMatrix'_mulVec]
    show D.psi.mulVec (g ((((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (coords D t F))) = _
    rw [← hx, Matrix.mulVecLin_apply, hg']
  refine ⟨_, fun x => ?_, hs⟩
  have hx : D.psi.mulVecLin (((D.r t : Kˣ) : K) • x) ∈ (D.V₀ t).map (D.v t).mulVecLin :=
    h t ▸ LinearMap.mem_range_self _ _
  obtain ⟨G, hG, hx⟩ := hx
  rw [← coords_range] at hG
  obtain ⟨F, rfl⟩ := hG
  refine ⟨F, D.psi_injective ?_⟩
  rw [Matrix.mulVecLin_apply, hs, ← Matrix.mulVecLin_apply, hx, map_smul, smul_smul, Units.inv_mul, one_smul]

def sideOf (h : OneForm D) : DefSide (baseOf D v0) where
  nV t := finrank K (D.V₀ t)
  HV _ := 1
  Mt t := (D.M t).comap ((coords D t).restrictScalars (𝓞 K))
  dQ _ := n
  Pq t := (exists_proj D h t).choose
  XQ _ := D.XE
  Qp _ := D.part
  dZ _ _ := 0
  HT _ _ := 1
  XT _ _ _ := 1
  Tl _ _ := ⊤
  Zp _ _ _ := ⊤

def dataOf (h : OneForm D) : IndefData (sideOf D v0 h) where
  μ := D.tup
  Tw := D.tup_finite.toFinset
  D := n
  XE := D.XE
  Ep := D.part
  ι _ := (1 : Matrix (Fin n) (Fin n) K)
  dW _ := 0
  XW _ _ := 1
  Wp _ _ := ⊤
  M _ := ⊤
  θ _ _ := (1 : Matrix (Fin 0) (Fin 0) K)
  κ := D.kap
  lam j _ c p := D.lam p j c
  err0 _ _ := 0

end Backward

end GlobalTheory.RowSlopeCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalTwoFormEqSumWedgeGlobalOneFormsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalTwoForm_eq_sumWedgeGlobalOneForms : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ ζ : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ζ T' = pOm F 2 φ (ζ T)) → ∃ (n : ℕ) (u v : Fin n → Glob1 F), ζ = wsum F u v := by
  first | exact @GlobalTheory.AbCoh.twoForm_eq_wsum | exact GlobalTheory.AbCoh.twoForm_eq_wsum | (intros; apply GlobalTheory.AbCoh.twoForm_eq_wsum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeEndProductPowersTransportGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeEndProductPowers_transport_grpPullback : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left := by
  first | (exact @GlobalTheory.ActFin.prod_zpow_transport) | (exact GlobalTheory.ActFin.prod_zpow_transport) | (intros; apply GlobalTheory.ActFin.prod_zpow_transport  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeRingActionIffEndomorphismRelationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupScheme_ringAction_iff_endomorphism_relations : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O), Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ) (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔ ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧ ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) := by
  first | exact @GlobalTheory.ActRel.ringAct_iff_relations | exact GlobalTheory.ActRel.ringAct_iff_relations | (intros; apply GlobalTheory.ActRel.ringAct_iff_relations <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbCoh

theorem prod_pullback_sq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap σ) φ → ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left, IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) ∧ μ[A'].left ≫ φ = Φ ≫ μ[A].left ∧ (fst A' A').left ≫ φ = Φ ≫ (fst A A).left ∧ (snd A' A').left ≫ φ = Φ ≫ (snd A A).left ∧ (lift (𝟙 A') (toUnit A' ≫ η[A'])).left ≫ Φ = φ ≫ (lift (𝟙 A) (toUnit A ≫ η[A])).left ∧ (lift (toUnit A' ≫ η[A']) (𝟙 A')).left ≫ Φ = φ ≫ (lift (toUnit A ≫ η[A]) (𝟙 A)).left := by
  intro R R' _ _ σ A _ A' _ φ h
  have pA : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have pA' : IsPullback (fst A' A').left (snd A' A').left A'.hom A'.hom := IsPullback.of_hasPullback _ _
  obtain ⟨Φ, h₁, h₂⟩ : ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left,
      Φ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ Φ ≫ (snd A A).left = (snd A' A').left ≫ φ :=
    ⟨pA.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ) (by
      rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc, ← Category.assoc, pA'.w]),
      pA.lift_fst _ _ _, pA.lift_snd _ _ _⟩
  have hP : IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) := by
    have q := pA'.paste_horiz h.1
    rw [← h₁, ← h.1.w] at q
    have r := (IsPullback.of_right q h₂ pA).paste_vert h.1
    rwa [Over.w, Over.w] at r
  have one : ∀ T : Over (Sp R'), (toUnit T ≫ η[A']).left ≫ φ = (T.hom ≫ spMap σ) ≫ η[A].left := by
    intro T
    let x₀ : Over.mk (T.hom ≫ spMap σ) ⟶ A := Over.homMk ((toUnit T ≫ η[A']).left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have e : x₀ = 1 := mul_eq_left.1 hx
    have e' := congrArg (fun q => q.left) e
    refine e'.trans ?_
    show (toUnit _ ≫ η[A]).left = _
    rw [Over.comp_left, Over.toUnit_left]
    rfl
  let Ψ : Over.mk ((A' ⊗ A').hom ≫ spMap σ) ⟶ A ⊗ A := Over.homMk Φ hP.w
  have hm := h.2 (A' ⊗ A') (fst A' A') (snd A' A') (Ψ ≫ fst A A) (Ψ ≫ snd A A) h₁ h₂
  rw [← MonObj.comp_mul, Hom.mul_def, Hom.mul_def, lift_fst_snd, lift_fst_snd, Category.id_comp, Category.id_comp,
    Over.comp_left] at hm
  refine ⟨Φ, hP, hm.symm, h₁.symm, h₂.symm, ?_, ?_⟩
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotientStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_conditions_of_etale_galois_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (Ga : Type) [Group Ga] (ρ : Ga → (o.A.left ⟶ o.A.left)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover Ga ρ ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ A', IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A'), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  first | exact @GlobalTheory.UPel.HT.EtaleLie.lie_of_etale | exact GlobalTheory.UPel.HT.EtaleLie.lie_of_etale | (intros; apply GlobalTheory.UPel.HT.EtaleLie.lie_of_etale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedDerivHilbertEisensteinSplitLatticeStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_iteratedDeriv_hilbertEisenstein_splitLattice : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (u : List (Emb F)), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (u.count i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)) (iterD u (fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  first | exact @GlobalTheory.HilbFam.hasSum_iterD_gval_split | exact GlobalTheory.HilbFam.hasSum_iterD_gval_split | (intros; apply GlobalTheory.HilbFam.hasSum_iterD_gval_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquation
section
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  intro hFE F _ _ _ hf 𝔞 𝔟
  have hD0 : (differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) ∈ (Ideal (𝓞 F))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  let D : (Ideal (𝓞 F))⁰ := ⟨_, hD0⟩
  obtain ⟨Zb, Zb', hZb, hZb', hFEb⟩ := hFE F (ClassGroup.mk F 𝔟)⁻¹ (ClassGroup.mk0 D * ClassGroup.mk F 𝔟) D rfl
    (by rw [mul_comm, mul_inv_cancel_right])
  obtain ⟨R, hR, hZR⟩ := GlobalTheory.T.partialZeta_totallyReal_at_most_simple_pole F _ _ Zb Zb' hZb hZb' hFEb
  obtain ⟨Za, Za', hZa, hZa', hFEa⟩ := hFE F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl
    (mul_inv_cancel_right _ _)
  have hgood : IsGood (gFun Zb 𝔞 𝔟) :=
    GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add F _ _ (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add F _ _ (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_of_sigma_only F _ (GlobalTheory.T.heckeEisensteinConstantTermPart_differentiableOn F 𝔞)) (GlobalTheory.T.heckeEisensteinZeroFrequencyPart_isSmoothHolomorphic F hf 𝔞 𝔟 Zb R hR hZR))
      (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_mul_left F _ _ ((kFac_differentiable.mul_const _).differentiableOn) (GlobalTheory.T.heckeEisensteinNonconstantFourierSum_smoothHolomorphic F 𝔞 𝔟))
  have hdF : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hcK : (cK F 2 : ℂ) ≠ 0 := by
    have : 0 < cK F 2 := by unfold cK; positivity
    exact_mod_cast this.ne'
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    have hn : 0 < nrm 𝔞 := by
      unfold nrm
      have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
      have h3 := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) h2.symm
      exact_mod_cast h3
    have : 0 < omegaFactor 𝔞 := by unfold omegaFactor; positivity
    exact_mod_cast this.ne'
  have hG0 : ∀ z, gFun Zb 𝔞 𝔟 0 z = aPart 𝔞 0 + kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z := by
    intro z; simp [gFun, bZero]
  have hB : ∀ z ∈ upperHalf F, kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z =
      (∑' c, qClass 𝔞 𝔟 2 z c) * (omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ) := by
    intro z hz
    rw [← (GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).2]
    field_simp
  refine ⟨gFun Zb 𝔞 𝔟, ⟨fun σ hσ z hz => GlobalTheory.T.heckeWeightTwoContinuation_eq_latticeSeries F 𝔞 𝔟 Zb hZb σ hσ z hz, hgood.1, hgood.2⟩, ?_, ?_⟩
  · refine DifferentiableOn.congr (f := fun z => aPart 𝔞 0 + (∑' c, qClass 𝔞 𝔟 2 z c) * ((omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ)))
      ?_ fun z hz => by rw [hG0, hB z hz, mul_div_assoc]
    apply DifferentiableOn.const_add
    apply DifferentiableOn.mul_const
    exact GlobalTheory.T.differentiableOn_hilbertEisensteinWeightTwoSeries F 𝔞 𝔟
  · refine ⟨Za', hZa', fun z hz => ⟨(GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).1, ?_⟩⟩
    rw [hG0, mul_add, add_div, GlobalTheory.T.heckeWeightTwo_constantTerm_eq_partialZeta_neg_one F 𝔞 _ D Za Za' rfl (mul_inv_cancel_right _ _) hZa hZa' hFEa,
      (GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).2]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingHensStatement
section
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselianLocalRing_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], HenselianLocalRing (Hens R) := by
  first | exact @GlobalTheory.Henselisation.henselianLocalRing_hens | exact GlobalTheory.Henselisation.henselianLocalRing_hens | (intros; apply GlobalTheory.Henselisation.henselianLocalRing_hens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolUnifCompLinearEquivExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.KeyFam

theorem holUnif_transport_linearEquiv : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  intro h A _ L u T
  have hc : Continuous T := T.toContinuousLinearEquiv.continuous
  have hd : Differentiable ℂ T := T.toContinuousLinearEquiv.differentiable
  let Λ' : Submodule ℤ (Fin h → ℂ) := u.Λ.comap ((T.restrictScalars ℤ).toLinearMap)
  have hmem : ∀ z, z ∈ Λ' ↔ T z ∈ u.Λ := fun z => Iff.rfl
  have hdisc : DiscreteTopology Λ' := by
    haveI := u.discrete
    let f : Λ' → u.Λ := fun z => ⟨T z, (hmem z).1 z.2⟩
    have hf : Continuous f := (hc.comp continuous_subtype_val).subtype_mk _
    have hi : Function.Injective f := fun a b hab =>
      Subtype.ext (T.injective (congrArg Subtype.val hab))
    exact DiscreteTopology.of_continuous_injective hf hi
  have hfull : Submodule.span ℝ (Λ' : Set (Fin h → ℂ)) = ⊤ := by
    have h1 : (Λ' : Set (Fin h → ℂ)) = (T.symm.restrictScalars ℝ).toLinearMap '' (u.Λ : Set (Fin h → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨T z, hz, by simp⟩
      · rintro ⟨w, hw, rfl⟩
        refine (hmem _).2 ?_
        simpa using hw
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact (T.symm.restrictScalars ℝ).surjective
  refine ⟨{ ex := fun z => u.ex (T z)
            ex_add := fun z w => by rw [map_add, u.ex_add]
            ex_onto := u.ex_onto.comp T.surjective
            Λ := Λ'
            ker := fun z => u.ker (T z)
            discrete := hdisc
            full := hfull
            hol := fun U f => ⟨(u.hol U f).1.preimage hc,
              (u.hol U f).2.comp hd.differentiableOn (fun _ hz => hz)⟩
            fr := fun i z => u.fr i (T z)
            fr_hol := fun i => (u.fr_hol i).comp hd.differentiableOn (fun _ hz => hz)
            fr_ne := fun i z hz => u.fr_ne i (T z) hz
            fr_compat := fun i j z hz => u.fr_compat i j (T z) hz }, fun _ => rfl, hmem⟩

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityComponentsSmoothGroupSchemeMulMemStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ w : (G ⊗ G).left, (fst G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (snd G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (μ[G]).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.IdCompMul.mul_mem | exact GlobalTheory.IdCompMul.mul_mem | (intros; apply GlobalTheory.IdCompMul.mul_mem <;> assumption)
end

