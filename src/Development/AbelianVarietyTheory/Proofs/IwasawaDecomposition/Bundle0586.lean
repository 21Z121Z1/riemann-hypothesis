import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSmulOfPreservesFrameOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.BadQNotOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0068
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0047
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
section
namespace GlobalTheory.UnipKill

noncomputable section

open ReciprocityTheory.ChartRestriction.G.FD NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem cc_add (x y : E) : cc (x + y) = cc x + cc y := map_add _ _ _
theorem cc_sub (x y : E) : cc (x - y) = cc x - cc y := map_sub _ _ _
theorem cc_mul (x y : E) : cc (x * y) = cc x * cc y := map_mul _ _ _
theorem cc_neg (x : E) : cc (-x) = -cc x := map_neg _ _
theorem cc_inv (x : E) : cc x⁻¹ = (cc x)⁻¹ := map_inv₀ _ _
theorem cc_one : cc (1 : E) = 1 := map_one _
theorem cc_zero : cc (0 : E) = 0 := map_zero _
theorem cc_natCast (n : ℕ) : cc (n : E) = n := map_natCast _ _
theorem cc_intCast (n : ℤ) : cc (n : E) = n := map_intCast _ _
theorem cc_two : cc (2 : E) = 2 := by simpa using cc_natCast (E := E) 2
theorem cc_cc (x : E) : cc (cc x) = x := IsCMField.complexConj_apply_apply E x
theorem cc_sum {ι : Type*} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) :=
  map_sum _ _ _
theorem cc_pow (x : E) (n : ℕ) : cc (x ^ n) = cc x ^ n := map_pow _ _ _
theorem cc_ofInt (x : 𝓞 E) : cc (x : E) = IsCMField.ringOfIntegersComplexConj E x := rfl

section herm

variable (G : Matrix (Fin N) (Fin N) E)

theorem herm_add_left (x x' y : Fin N → E) : herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (x y y' : Fin N → E) : herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, Pi.add_apply, cc_add, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (c : E) (x y : Fin N → E) : herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_smul_right (c : E) (x y : Fin N → E) : herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_neg_left (x y : Fin N → E) : herm G (-x) y = - herm G x y := by
  rw [show -x = (-1 : E) • x by simp, herm_smul_left]; ring

theorem herm_neg_right (x y : Fin N → E) : herm G x (-y) = - herm G x y := by
  rw [show -y = (-1 : E) • y by simp, herm_smul_right, cc_neg, cc_one]; ring

theorem herm_sub_left (x x' y : Fin N → E) : herm G (x - x') y = herm G x y - herm G x' y := by
  rw [sub_eq_add_neg, herm_add_left, herm_neg_left, sub_eq_add_neg]

theorem herm_sub_right (x y y' : Fin N → E) : herm G x (y - y') = herm G x y - herm G x y' := by
  rw [sub_eq_add_neg, herm_add_right, herm_neg_right, sub_eq_add_neg]

theorem herm_zero_right (x : Fin N → E) : herm G x 0 = 0 := by simp [herm, cc_zero]

theorem cc_herm (hG : ∀ a b, cc (G a b) = G b a) (x y : Fin N → E) :
    cc (herm G x y) = herm G y x := by
  simp only [herm, cc_sum, cc_mul, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_single (x : Fin N → E) (b : Fin N) :
    herm G x (Pi.single b 1) = ∑ a, x a * G a b := by
  simp [herm, Pi.single_apply, apply_ite cc, cc_one, cc_zero, mul_ite, Finset.sum_ite_eq']

theorem eq_zero_of_herm (hG : G.det ≠ 0) (x : Fin N → E) (h : ∀ y, herm G x y = 0) : x = 0 := by
  have h1 : Matrix.vecMul x G = 0 := by
    ext b
    have := h (Pi.single b 1)
    rw [herm_single] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have hu : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 (isUnit_iff_ne_zero.2 hG)
  have := Matrix.vecMul_injective_of_isUnit hu (a₁ := x) (a₂ := 0)
  simpa using this (by simpa using h1)

end herm

def rk1 (G : Matrix (Fin N) (Fin N) E) (u v : Fin N → E) : Matrix (Fin N) (Fin N) E :=
  Matrix.of fun a b => u a * ∑ k, G b k * cc (v k)

theorem one_add_smul_vecMulVec_mulVec (G : Matrix (Fin N) (Fin N) E) (u v x : Fin N → E) :
    (rk1 G u v).mulVec x = herm G x v • u := by
  ext a
  simp only [Matrix.mulVec, dotProduct, rk1, Matrix.of_apply, herm, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

theorem one_add_smul_vecMulVec_mul (G : Matrix (Fin N) (Fin N) E) (u v u' v' : Fin N → E) :
    rk1 G u v * rk1 G u' v' = herm G u' v • rk1 G u v' := by
  rw [Matrix.ext_iff_mulVec]; intro x
  rw [← Matrix.mulVec_mulVec, one_add_smul_vecMulVec_mulVec, one_add_smul_vecMulVec_mulVec, herm_smul_left, Matrix.smul_mulVec,
    one_add_smul_vecMulVec_mulVec, smul_smul, mul_comm]

theorem rk1_smul_left (G : Matrix (Fin N) (Fin N) E) (c : E) (u v : Fin N → E) :
    rk1 G (c • u) v = c • rk1 G u v := by
  ext a b; simp [rk1]; ring

theorem rk1_smul_right (G : Matrix (Fin N) (Fin N) E) (c : E) (u v : Fin N → E) :
    rk1 G u (c • v) = cc c • rk1 G u v := by
  ext a b; simp [rk1, cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem transvMat_eq (G : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (α : E) :
    transvMat G ξ α = 1 + α • rk1 G ξ ξ := by
  ext a b; simp [transvMat, rk1, Matrix.one_apply]; ring

def IsIsom (G : Matrix (Fin N) (Fin N) E) (A : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ x y, herm G (A.mulVec x) (A.mulVec y) = herm G x y

def IsSkew (G : Matrix (Fin N) (Fin N) E) (A : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ x y, herm G (A.mulVec x) y = - herm G x (A.mulVec y)

variable (G : Matrix (Fin N) (Fin N) E)

theorem herm_mulVec_mulVec_eq_zero {A : Matrix (Fin N) (Fin N) E} (hA : IsSkew G A)
    (h2 : A * A = 0) (x y : Fin N → E) : herm G (A.mulVec x) (A.mulVec y) = 0 := by
  rw [hA, Matrix.mulVec_mulVec, h2]; simp [herm_zero_right]

theorem isSkew_sub_one {A : Matrix (Fin N) (Fin N) E} (hA : IsIsom G A) (h2 : (A - 1) * (A - 1) = 0) :
    IsSkew G (A - 1) := by
  intro x y
  have hinv : A * (1 - (A - 1)) = 1 := by
    have : A * (1 - (A - 1)) = 1 - (A - 1) * (A - 1) := by noncomm_ring
    rw [this, h2, sub_zero]
  have key : herm G (A.mulVec x) y = herm G x ((1 - (A - 1)).mulVec y) := by
    conv_rhs => rw [← hA x ((1 - (A - 1)).mulVec y), Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, herm_sub_left, herm_sub_right, key]
  ring

theorem one_add_pow_of_sq_eq_zero {n : Matrix (Fin N) (Fin N) E} (h2 : n * n = 0) (k : ℕ) :
    (1 + n) ^ k = 1 + (k : E) • n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, h2, smul_zero, add_zero,
      Nat.cast_succ, add_smul, one_smul]
    abel

theorem transvMat_mul_transvMat (ξ ξ' : Fin N → E) (h : herm G ξ' ξ = 0) (α β : E) :
    transvMat G ξ α * transvMat G ξ' β = 1 + (α • rk1 G ξ ξ + β • rk1 G ξ' ξ') := by
  rw [transvMat_eq, transvMat_eq, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, mul_smul_comm,
    one_add_smul_vecMulVec_mul, h, zero_smul, smul_zero, smul_zero]
  abel

theorem transvMat_mul_self (ξ : Fin N → E) (h : herm G ξ ξ = 0) (α β : E) :
    transvMat G ξ α * transvMat G ξ β = transvMat G ξ (α + β) := by
  rw [transvMat_mul_transvMat G ξ ξ h, transvMat_eq, add_smul]

theorem transvMat_pow (ξ : Fin N → E) (h : herm G ξ ξ = 0) (α : E) (k : ℕ) :
    transvMat G ξ α ^ k = transvMat G ξ (k * α) := by
  induction k with
  | zero => simp [transvMat_eq]
  | succ k ih => rw [pow_succ, ih, transvMat_mul_self G ξ h, Nat.cast_succ]; congr 1; ring

end

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.PtComp

theorem disjoint_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (hsm : Smooth f)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  refine CompSplitPfD.cspD_disj (fun x => ?_) Z Z' hZ hZ' hne
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have h1 := HasRingHomProperty.appLE (P := @Smooth) f hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp)
  let ψ : K →+* Γ(X, V) :=
    (f.appLE ⊤ V (fun p _ => by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have : Algebra.Smooth K Γ(X, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) K) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) K) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

theorem connectedComponent_mem {X : Type} [TopologicalSpace X] (hfin : (irreducibleComponents X).Finite)
    (hd : ∀ Z ∈ irreducibleComponents X, ∀ Z' ∈ irreducibleComponents X, Z ≠ Z' → Disjoint Z Z') (z : X) :
    connectedComponent z ∈ irreducibleComponents X ∧ IsOpen (connectedComponent z) := by
  have hV := irreducibleComponent_mem_irreducibleComponents z
  have hU : irreducibleComponent z = (⋃ W ∈ irreducibleComponents X \ {irreducibleComponent z}, W)ᶜ := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro hp W hW hpW
      exact Set.disjoint_left.1 (hd _ hW.1 _ hV hW.2) hpW hp
    · intro hp
      by_contra hpZ
      exact hp _ ⟨irreducibleComponent_mem_irreducibleComponents p,
        fun h => hpZ ((show irreducibleComponent p = _ from h) ▸ mem_irreducibleComponent)⟩ mem_irreducibleComponent
  have ho : IsOpen (irreducibleComponent z) := by
    rw [hU]
    exact ((hfin.subset Set.diff_subset).isClosed_biUnion fun W hW =>
      isClosed_of_mem_irreducibleComponents _ hW.1).isOpen_compl
  have e : connectedComponent z = irreducibleComponent z :=
    ((IsClopen.connectedComponent_subset ⟨isClosed_irreducibleComponent, ho⟩ mem_irreducibleComponent)).antisymm
      irreducibleComponent_subset_connectedComponent
  rw [e]
  exact ⟨hV, ho⟩

theorem exists_point {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω] {X : Scheme.{0}} (π : X ⟶ Sp K)
    [LocallyOfFiniteType π] (x : Sp Ω ⟶ Sp K) {O : Set X} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ g : Sp Ω ⟶ X, g ≫ π = x ∧ ∀ a, g a ∈ O := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint Ω)
    (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := pullback.fst π x ⁻¹' O)
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (hO.preimage (pullback.fst π x).continuous).isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem preimage_connectedComponent_mem (Z : Model Xo c β) (hsm : Smooth (genStr Z)) (z : gen Z) :
    Z.jQ ⁻¹' connectedComponent z ∈ irreducibleComponents (Xo.XF c) := by
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  obtain ⟨h1, h2⟩ := connectedComponent_mem TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => disjoint_of_smooth (genStr Z) hsm W W' hW hW') z
  have := Z.jQ_open
  exact preimage_mem_irreducibleComponents h1 Z.jQ.isOpenEmbedding
    (Z.jQ_dense.inter_open_nonempty _ h2 ⟨z, mem_connectedComponent⟩)

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

theorem exists_equiv : ∃ q : s.Comp ≃ Comp (S.Xo κ.l) κ.c, ∀ k z,
    OnComp s k z ↔ (q k).1 = s.T.Z.jQ ⁻¹' connectedComponent z := by
  have hσ : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl
  have hne : ∀ k, ((s.U κ.σ₀).X k).dom.Nonempty := fun k => GlobalTheory.OrbitScalar.exists_mem_dom _
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp _ _ _ _ _ _ κ.σ₀ N (s.U κ.σ₀) hσ (s.unf _ hσ).1 hne s.geo
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q, fun k z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨x, hx⟩
    by_contra hn
    let pt : Sp (CAt κ.σ₀) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ (q k)
      ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩ fun e => hn (congrArg Subtype.val e)) (hq k x pt) (hx pt)
  · obtain ⟨x, hx⟩ := hne k
    refine ⟨⟨x, hx⟩, fun pt => ?_⟩
    have := hq k ⟨x, hx⟩ pt
    rw [h] at this
    exact this

theorem existsUnique_onComp (z : gen s.T.Z) : ∃! k, OnComp s k z := by
  obtain ⟨q, hq⟩ := exists_equiv s
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q.symm ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩, (hq _ _).2 (by rw [Equiv.apply_symm_apply]),
    fun k hk => ?_⟩
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext ((hq _ _).1 hk)

theorem onComp_compPt (y : Pt s) (pt : Sp Qb) : OnComp s (compPt s y) (y.y pt) := by
  obtain ⟨k, hk, -⟩ := existsUnique_onComp s (y.y pt)
  have : ∃ k, ∀ pt', OnComp s k (y.y pt') :=
    ⟨k, fun pt' => (Subsingleton.elim (α := PrimeSpectrum Qb) pt pt') ▸ hk⟩
  exact Classical.epsilon_spec this pt

theorem compPt_surjective : Function.Surjective (compPt s) := by
  intro k
  obtain ⟨q, hq⟩ := exists_equiv s
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  have := s.T.Z.jQ_open
  have := κ.c.fin
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  let φ : κ.c.F →+* Qb := (IsAlgClosed.lift : κ.c.F →ₐ[ℚ] Qb).toRingHom
  have ho : IsOpen (q k).1 := (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj _ _) (q k)).isOpen
  obtain ⟨g, hg, hgO⟩ := exists_point (genStr s.T.Z) (spMap φ) (s.T.Z.jQ.isOpenEmbedding.isOpenMap _ ho)
    ((q k).2.1.nonempty.image _)
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ s.T.Z Qb φ g hg
  let y : Pt s := ⟨φ, g, hg, f.v, f.tan, f.eig, f.basis⟩
  let pt : Sp Qb := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Qb)
  obtain ⟨a, ha, hag⟩ := hgO pt
  refine ⟨y, (existsUnique_onComp s (g pt)).unique (onComp_compPt s y pt) ((hq _ _).2 ?_)⟩
  by_contra hn
  refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ (q k)
    ⟨_, preimage_connectedComponent_mem s.T.Z hsm (g pt)⟩ fun e => hn (congrArg Subtype.val e)) ha ?_
  show s.T.Z.jQ a ∈ connectedComponent (g pt)
  rw [hag]
  exact mem_connectedComponent

end GlobalTheory.ShFam.PtComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceNoChainPlaceOrTypePrimeOver
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

namespace GlobalTheory.ServedPlace

theorem places_prime : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v ∧
        (∀ w' ∈ Formalism.L2.Forms.badQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)), (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal) ∧
        ¬ (w.D Z).what₂.places.resChar v ∣ ((w.D Z).mem u).A.T := by
  intro K B f T w hK hF hP Z t Wt nch n Y hMu hQ O hO hU E hE Fl hfl hw u v hg hμ tt hStd
  have hok : Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v := by
    intro w' hw' hpw
    obtain ⟨P0, hP0, hu⟩ := (tt.ch.Q_iff _ w').1 hw'
    rw [n.xi] at hu
    have hq := GlobalTheory.Mem.ReadTwist.mem_qprime_iff (w.ok.xi_reads ((w.D Z).what₂.muAt v)) w'
    have hab : P0.under (𝓞 (w.D Z).host.F) = w' := by
      unfold Formalism.L2.Host.aboveF at hP0
      rw [Set.Finite.mem_toFinset] at hP0
      exact hP0
    have hv := hq.2 ⟨P0, hab, hu⟩
    have hPQ : w.I.sel w' ∈ ColIn.Q w.I ((w.D Z).what₂.muAt v) :=
      (Formalism.L2.Col.mem_QE w.I.sel (w.I.tup _) _).2 ⟨w', hv, rfl⟩
    have hund : (w.I.sel w').under (𝓞 B.host.F) = w' := GlobalTheory.TwistPlaces.under_eq_iff.2 (w.ok.sel_ok w')
    have hp : Nat.Prime ((w.D Z).what₂.places.resChar v) := hg.1
    have hmem : ((((w.D Z).what₂.places.resChar v : ℕ)) : 𝓞 B.host.E) ∈ (w.I.sel w').asIdeal := by
      rw [← hund] at hpw
      have := hpw
      simp only [HeightOneSpectrum.under, Ideal.under, Ideal.mem_comap, map_natCast] at this
      exact this
    have hQp := (hQ ((w.D Z).what₂.muAt v) ((w.D Z).what₂.places.resChar v)).2 ⟨hp, w.I.sel w', hPQ, hmem⟩
    exact Y.Qp_muAt v hQp
  exact ⟨hok, fun w' hw' => Formalism.MainNotions.G.CmpJ.badQ_notOver u v hg _ hok w' hw', hg.2.2.2.2.2⟩

end GlobalTheory.ServedPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPower
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem det_blocks_lower {S J : Type} [CommRing S] [Fintype J] [DecidableEq J] (m : J → ℕ)
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) (hz : ∀ τ i j, i < j → g τ i j = 0) {n : ℕ}
    (e : Fin n ≃ Σ τ : J, Fin (m τ)) :
    ((Matrix.blockDiagonal' g).submatrix e e).det = ∏ x : (Σ τ : J, Fin (m τ)), g x.1 x.2 x.2 := by
  rw [Matrix.det_submatrix_equiv_self, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun τ _ => Matrix.det_of_lowerTriangular _ fun i j hij => hz τ i j hij

theorem isCombAt_blocks {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {J : Type} [Fintype J] [DecidableEq J] {m : J → ℕ}
    (u : ∀ τ, Fin (m τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ τ i, IsTanAt x (u τ i))
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) {n : ℕ} (e : Fin n ≃ Σ τ : J, Fin (m τ)) (i : Fin n)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (h : IsCombAt x (u (e i).1) (g (e i).1 (e i).2) w) :
    IsCombAt x (fun j => u (e j).1 (e j).2) ((Matrix.blockDiagonal' g).submatrix e e i) w := by
  obtain ⟨N, _, _, v, ρ, -, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (hu τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  rw [hcomb] at h ⊢
  rw [h]
  congr 1
  simp only [Matrix.submatrix_apply]
  rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => Matrix.blockDiagonal' g (e i) p • b p.1 p.2), Fintype.sum_sigma]
  generalize e i = p
  obtain ⟨a, k⟩ := p
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro σ _ hσ
    simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hσ.symm, zero_smul, Finset.sum_const_zero]
  · simp

theorem rule_frBor : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (t : Ix Dw → Kˣ) (y y' : FrPt Xo c K) (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x), FrBor t y y' → Tied e y.s y.u Φ → Tied e y'.s y'.u Φ' → κ K Φ'.key = kch t ^ 4 * κ K Φ.key := by
  classical
  intro κ hH hF E _ _ _ H Dw l Xo c g e K _ _ _ t y y' Φ Φ' hb hT hT'
  obtain ⟨M, hz, hd, hx, hc, hs⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 hb
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hc hs Φ Φ' hT hT'
  subst hx
  obtain ⟨h1, hg, hv⟩ := hT
  obtain ⟨h1', hg', hv'⟩ := hT'
  subst hg'
  have hid : x' = spMap (RingHom.id K) ≫ x' := by rw [GlobalTheory.Frames.SecCalc.spMap_id', Category.id_comp]
  have did : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    have hd : dualMap (RingHom.id K) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [hd]
    exact Spec.map_id _
  obtain ⟨th, hth⟩ := (GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.1 s
  have hne := ((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.2 th s hth).2.1
    (((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ.T.t Φ.m).2.2 Φ.th s h1).2.2 Φ.th_ne)
  have hss : GlobalTheory.Frames.SecBC (RingHom.id K) 1 x' x' s s :=
    ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo K K K _ _ x' x' x' hid hid).2.1 1 s s).2 fun i => by
      rw [GlobalTheory.Frames.SecCalc.scal_one', _root_.one_mul]
  obtain ⟨hg2, v, hvb, hpb, hvv⟩ := fibKey_keyPB E H Dw l Xo K K (RingHom.id K) x' x' Φ
    { Φ' with th := th, th_ne := hne } s s hid h1 hth hss
  have hvu : ∀ i : Fin Φ'.T.g, (v i).left ≫ Φ'.m.φ = u (e i).1 (e i).2 := fun i => by
    refine (hvv i).trans ?_
    rw [did, Category.id_comp]
    exact hv _
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have hsc := ((TieCalc.secTie_calc E H Dw l Xo K x' Φ'.T.t Φ'.m th s hth).1 _ x' s' Φ'.th rfl hs).1 h1'
  have hcomb : ∀ i, IsLieComb ((Matrix.blockDiagonal' M).submatrix e e i) v (Φ'.v i) := fun i => by
    have h2 := isCombAt_blocks u tan M e i _ (hc (e i).1 (e i).2)
    rw [← funext hvu] at h2
    obtain ⟨w, hw, hw'⟩ := (GlobalTheory.MetricChange.lift_comb Φ'.m.cart).2 _ _ v _ h2
    have : w = Φ'.v i := Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext (hw.trans (hv' i).symm) ((Over.w _).trans (Over.w _).symm))
    exact this ▸ hw'
  have e2 := hH K Φ'.T.pol Φ'.g_pos Φ'.T.t.PP.rig Φ'.T.t.PP.rigGen th hne v hvb Φ'.th Φ'.th_ne Φ'.v Φ'.basis
    (t none : K) _ hsc hcomb
  have e3 := (det_blocks_lower (fun τ => Dw.mult τ) M hz e).trans (Finset.prod_congr rfl fun x _ => hd x.1 x.2)
  have e4 : ((t none : K)) ^ 8 * (κ K Φ'.key : K) =
      (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (t (some x) : K)) ^ 4 * (κ K Φ.key : K) := by
    refine e2.trans ?_
    exact congrArg₂ (fun a b : K => a ^ 4 * b) e3 e1
  apply Units.ext
  have h0 : (t none : K) ≠ 0 := Units.ne_zero _
  rw [kch_eq]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_prod]
  field_simp
  linear_combination e4

end GlobalTheory.KeyFourth
end

