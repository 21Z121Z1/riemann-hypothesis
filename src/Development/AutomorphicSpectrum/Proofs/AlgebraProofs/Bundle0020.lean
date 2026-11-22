import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FirstLatticeBaseChange
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.WeilBound.CoreStatements.HodgeTatePoints.RbProj
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0008
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormStable

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂] (r r₂ : ℕ) (L : AddSubgroup E) (C C' : AddSubgroup E₂) (Δ : AddSubgroup (E × E₂)), LocFree R r L → LocFree R r₂ C → LocFree R r₂ C' → (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → (∀ v w, (v, w) ∈ Δ → v ∈ L ∧ w ∈ C) → (∀ v ∈ L, ∃ w, (v, w) ∈ Δ) → (∀ w, (0, w) ∈ Δ ↔ w ∈ C') → (∀ w ∈ C, ∃ v, (v, w) ∈ Δ) → LocFree R (r + r₂) Δ ∧ LocFree R r (Δ.comap (AddMonoidHom.inl E E₂)) := by
  intro o Ω _ _ _ R E E₂ _ _ _ _ r r₂ L C C' Δ hL hC hC' hsm hsub hliftL hker hliftC
  have hC'eq : AddSubgroup.comap (LinearMap.inr Ω E E₂).toAddMonoidHom Δ = C' := by
    ext w
    change (0, w) ∈ Δ ↔ w ∈ C'
    exact hker w
  have hLeq : AddSubgroup.map (LinearMap.fst Ω E E₂).toAddMonoidHom Δ = L := by
    ext v
    constructor
    · rintro ⟨⟨v', w⟩, h, rfl⟩
      exact (hsub v' w h).1
    · intro hv
      obtain ⟨w, hw⟩ := hliftL v hv
      exact ⟨(v, w), hw, rfl⟩
  have hCeq : AddSubgroup.map (LinearMap.snd Ω E E₂).toAddMonoidHom Δ = C := by
    ext w
    constructor
    · rintro ⟨⟨v, w'⟩, h, rfl⟩
      exact (hsub v w' h).2
    · intro hw
      obtain ⟨v, hv⟩ := hliftC w hw
      exact ⟨(v, w), hv, rfl⟩
  have hΔ : LocFree R (r + r₂) Δ := by
    have h := GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt.main R (LinearMap.inr Ω E E₂) (LinearMap.fst Ω E E₂)
      LinearMap.inr_injective LinearMap.fst_surjective
      (LinearMap.range_inr (R := Ω) (M := E) (M₂ := E₂)) Δ r₂ r hsm
      (by rw [hC'eq]; exact hC') (by rw [hLeq]; exact hL)
    rwa [Nat.add_comm] at h
  refine ⟨hΔ, ?_⟩
  have h := GlobalTheory.T.locally_free_of_short_exact R (LinearMap.inl Ω E E₂) (LinearMap.snd Ω E E₂)
    LinearMap.inl_injective LinearMap.snd_surjective
    (LinearMap.range_inl (R := Ω) (M := E) (M₂ := E₂)) Δ r r₂ hΔ (by rw [hCeq]; exact hC)
  have he : (LinearMap.inl Ω E E₂).toAddMonoidHom = AddMonoidHom.inl E E₂ := by
    ext x <;> simp
  rw [he] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChange
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, LocFree R n (D.af R p (χ τ)) ∧ LocFree R n (D.hh R p (χ τ)) ∧ D.af R p (χ τ) ≤ stdLat R _ ∧ ∀ i, LocFree R 1 (D.xId (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₁ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).af RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.af R p (χ τ)) ∧ (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.hh R p (χ τ)) ∧ ∀ i, (D.bc RC).xId (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
  exact @PositivityTheory.Xgn.good_lattice_base_change

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LinearIndependentMapVec
section
noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubFrob

variable {K : Type} [Field K]

theorem repr_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b : Module.Basis (Fin n) K V)
    (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (x : V) (j : Fin n) :
    b'.repr (F x) j = σ (b.repr x j) := by
  have hx : F x = ∑ k, σ (b.repr x k) • b' k := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.map_smulₛₗ, h]
  rw [hx, b'.repr_sum_self]

theorem det_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b c : Module.Basis (Fin n) K V)
    (b' c' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (hc : ∀ j, c' j = F (c j)) :
    b'.det c' = σ (b.det c) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hc]
  exact repr_semilinear F b b' h _ _

theorem isLatOf_spanLat (C : ACurve K) {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ}
    (L : C.I → AddSubgroup V) (i : C.I) (hσ : ∀ a, C.v i a ≤ 1 → C.v i (σ a) ≤ 1)
    (b : Module.Basis (Fin n) K V) (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j))
    (hL : IsLatOf C i b (L i)) : IsLatOf C i b' (spanLat C L F i) := by
  intro y
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, ha, hx, rfl⟩ := hy
      intro q
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, repr_semilinear F b b' h]
      exact mul_le_one' ha (hσ _ ((hL x).1 hx q))
    | zero => intro q; simp
    | add x y _ _ hx hy =>
      intro q
      rw [map_add, Finsupp.add_apply]
      exact (C.v i).map_add_le (hx q) (hy q)
    | neg x _ hx =>
      intro q
      rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]
      exact hx q
  · intro hy
    rw [← b'.sum_repr y]
    refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ⟨_, b k, hy k, ?_, by rw [h]⟩
    rw [hL]
    intro q
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem isLatOf_comap (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V] (i : C.I)
    {m r : ℕ} (L : AddSubgroup V) (W : Submodule K V) (b : Module.Basis (Fin (m + r)) K V)
    (c : Module.Basis (Fin m) K W) (h : ∀ j, b (Fin.castAdd _ j) = c j) (hL : IsLatOf C i b L) :
    IsLatOf C i c (L.comap W.subtype.toAddMonoidHom) := by
  intro x
  have hx : (x : V) = ∑ k, (Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k) • b k := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, zero_smul, Finset.sum_const_zero, add_zero, h]
    have := congrArg W.subtype (c.sum_repr x)
    rw [map_sum] at this
    exact this.symm
  have hr : ∀ k, b.repr (x : V) k =
      Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k := by
    intro k
    conv_lhs => rw [hx, b.repr_sum_self]
  rw [AddSubgroup.mem_comap]
  change (x : V) ∈ L ↔ _
  rw [hL]
  constructor
  · intro H q
    have := H (Fin.castAdd _ q)
    rwa [hr, Fin.addCases_left] at this
  · intro H q
    rw [hr]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) q
    · rw [Fin.addCases_left]; exact H j
    · rw [Fin.addCases_right]; simp

def mapVec (σ : K →+* K) (d : ℕ) : (Fin d → K) →ₛₗ[σ] (Fin d → K) where
  toFun x := fun j => σ (x j)
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

theorem linearIndependent_mapVec (σ : K →+* K) {d n : ℕ} (v : Fin n → Fin d → K)
    (hv : LinearIndependent K v) : LinearIndependent K (fun j => mapVec σ d (v j)) := by
  have h1 : Function.Injective (Matrix.of v).vecMulLinear := by
    have := Matrix.vecMul_injective_iff.2 (show LinearIndependent K (Matrix.of v).row from hv)
    exact this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 h1)
  set B : Matrix (Fin d) (Fin n) K := LinearMap.toMatrixRight' g with hB
  have hgB : ∀ x, g x = Matrix.vecMul x B := by
    intro x
    have : Matrix.toLinearMapRight' B = g := by
      rw [hB]; exact LinearMap.toMatrixRight'.symm_apply_apply g
    rw [← this]; rfl
  have h2 : Matrix.of v * B = 1 := by
    ext a b
    have := congrFun (LinearMap.congr_fun hg (Pi.single a 1)) b
    simp only [LinearMap.comp_apply, hgB, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
      LinearMap.id_apply, Matrix.single_one_vecMul] at this
    rw [Matrix.one_apply]
    change Matrix.vecMul (v a) B b = _
    simpa [Pi.single_apply, eq_comm] using this
  have h3 : (Matrix.of v).map σ * B.map σ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ σ.map_zero σ.map_one]
  have h4 : LinearIndependent K ((Matrix.of v).map σ).row := by
    rw [← Matrix.vecMul_injective_iff]
    intro x y hxy
    have := congrArg (fun z => Matrix.vecMul z (B.map σ)) hxy
    simpa [Matrix.vecMul_vecMul, h3] using this
  exact h4

theorem exists_basis_top (σ : K →+* K) {d n : ℕ} (b : Module.Basis (Fin n) K (Fin d → K)) :
    ∃ b' : Module.Basis (Fin n) K (Fin d → K), ∀ j, b' j = mapVec σ d (b j) :=
  ⟨basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_mapVec σ b b.linearIndependent)
    (Module.finrank_eq_card_basis b).symm, fun j => by simp⟩

theorem exists_basis_sub (σ : K →+* K) {d n : ℕ} (W : Submodule K (Fin d → K))
    (c : Module.Basis (Fin n) K W) :
    ∃ c' : Module.Basis (Fin n) K (Submodule.span K (mapVec σ d '' (W : Set (Fin d → K)))),
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
  have hli := linearIndependent_mapVec σ (fun j => (c j : Fin d → K))
    (c.linearIndependent.map' W.subtype W.ker_subtype)
  have hs : Submodule.span K (Set.range fun j => mapVec σ d (c j)) =
      Submodule.span K (mapVec σ d '' (W : Set (Fin d → K))) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨c j, (c j).2, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have : x = ∑ k, c.repr ⟨x, hx⟩ k • (c k : Fin d → K) := by
        have := congrArg W.subtype (c.sum_repr ⟨x, hx⟩)
        rw [map_sum] at this
        exact this.symm
      rw [this, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs), fun j => ?_⟩
  simp [Module.Basis.span_apply]

theorem subDeg_frob : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W : Submodule K (Fin d → K)), IsBun C L → subDeg C (frobLat C p L) (frobSub p W) = p * subDeg C L W := by
  intro K _ C p _ _ d L W hL
  set σ := frobenius K p with hσ
  have hL' : IsBun C (frobLat C p L) := (GlobalTheory.T.frobenius_lattice_degree_mul_p K C p d L hL).1
  have hS := (GlobalTheory.T.sub_and_quotient_bundles K C _ L W hL).1
  have hS' := (GlobalTheory.T.sub_and_quotient_bundles K C _ _ (frobSub p W) hL').1
  have hv : ∀ i a, C.v i (σ a) = C.v i a ^ p := fun i a => by rw [hσ, frobenius_def, map_pow]
  have key : ∀ i, ∃ (c : Module.Basis (Fin (Module.finrank K W)) K W)
      (c' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W)),
      IsLatOf C i c (sub C L W i) ∧ IsLatOf C i c' (sub C (frobLat C p L) (frobSub p W) i) ∧
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
    intro i
    obtain ⟨b, hb⟩ := hL.1 i
    obtain ⟨c, -, b₁, hb₁, hc, -, hbc, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C _ i _ b (L i) W hb
    obtain ⟨b', hb'⟩ := exists_basis_top σ b₁
    obtain ⟨c', hc'⟩ := exists_basis_sub σ W c
    refine ⟨c, c', hc, ?_, hc'⟩
    refine isLatOf_comap C i _ _ b' c' (fun j => by rw [hb', hbc]; exact (hc' j).symm) ?_
    exact isLatOf_spanLat C (mapVec σ d) L i (fun a ha => by rw [hv]; exact pow_le_one' ha p)
      b₁ b' hb' hb₁
  choose c c' hc hc' hcc using key
  obtain ⟨e', he'⟩ : ∃ e' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W),
      ∀ j, (e' j : Fin d → K) = mapVec σ d (Module.finBasis K W j) :=
    exists_basis_sub σ W (Module.finBasis K W)
  let G : W →ₛₗ[σ] frobSub p W :=
    ((mapVec σ d).domRestrict W).codRestrict (frobSub p W)
      (fun x => Submodule.subset_span ⟨x, x.2, rfl⟩)
  obtain ⟨-, h1⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ _ _ (Module.finBasis K W) c hS hc
  obtain ⟨-, h2⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ _ _ e' c' hS' hc'
  unfold subDeg
  rw [h1, h2, mul_finsum]
  refine finsum_congr fun i => ?_
  have hd := det_semilinear G (Module.finBasis K W) (c i) e' (c' i)
    (fun j => Subtype.ext (he' j)) (fun j => Subtype.ext (hcc i j))
  rw [hd, hv, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Crv.SubFrob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeTestPointMembershipStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_test_point_membership : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ {ι : Type} [Fintype ι] (N : ℕ) (L : AddSubgroup (ι → Ω)), LocFree R N L → ∀ v : ι → Ω, (∃ m : ℕ, (p : Ω) ^ m • v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → bcMap Ω C ι v ∈ spanOver RC (bcMap Ω C ι '' L)) → v ∈ L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main | exact GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NegDefBlockOfPosDefStatement
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negDef_block_of_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef | exact GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacter
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem eigencomponents_scalars : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ g ∈ augIdeal AA.carrier, (∀ χ : MulChar F R, proj χ g ∈ eig AA.carrier χ) ∧ g = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g ∧ (g ∈ afFun p AA.carrier → ∀ χ : MulChar F R, proj χ g ∈ afFun p AA.carrier) ∧ (∀ K : Submodule F N, g ∈ invFun AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, proj χ g ∈ invFun AA.carrier K.toAddSubgroup) ∧ (g ∈ sqIdeal (augIdeal AA.carrier) → ∀ χ : MulChar F R, proj χ g ∈ sqIdeal (augIdeal AA.carrier)) :=
  @PositivityTheory.HtPt.Rb.proj_props

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupLength
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem idealD_pow_mem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) :=
  @PositivityTheory.HtPt.Rd.a_pow

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialPolarizedAbelianPointEqOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DimZero

theorem isIso_hom_of_relDim_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension 0 A.hom) : IsIso A.hom := by
  haveI := h.proper
  haveI := h.geomConnected
  haveI : Etale A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hd
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ A.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.hom
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl
  haveI : IsOpenImmersion e :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) e A.hom
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal A.hom))) (by rw [he]; infer_instance)
  have hs : ∀ y : S, A.hom (e y) = y := fun y => by rw [← Scheme.Hom.comp_apply, he]; rfl
  haveI : IsIso e := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (top_unique fun a _ => ?_)
    have hc := (A.hom.isConnected_preimage_singleton (A.hom a)).isPreconnected
    have hcl : IsClopen (Set.range e) :=
      ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
    exact hc.subset_isClopen hcl ⟨e (A.hom a), hs _, _, rfl⟩ rfl
  haveI : IsIso (e ≫ A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e _

theorem over_hom_eq_of_mono {S : Scheme.{0}} {T A : Over S} [Mono A.hom] (x y : T ⟶ A) : x = y := by
  ext1
  rw [← cancel_mono A.hom, Over.w x, Over.w y]

theorem eq_one_of_g_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (hg : P.g = 0) (z : sp (R₀ := R) R ⟶ P.A) :
    z = 1 := by
  have hd : SmoothOfRelativeDimension 0 P.A.hom := hg ▸ P.smoothDim
  haveI := isIso_hom_of_relDim_zero P.A P.isAb hd
  exact over_hom_eq_of_mono _ _

end GlobalTheory.CompanionTheory.Ar.DimZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormStableStatement
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_det_norm_stable : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close | exact GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close <;> assumption)
end

