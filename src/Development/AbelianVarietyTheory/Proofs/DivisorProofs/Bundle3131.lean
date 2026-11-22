import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantComm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.RegCommutant

theorem exists_not_commute_of_two_le_finrank {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (h : 2 ≤ Module.finrank K E) :
    ∃ S₁ S₂ : Module.End K E, S₁ * S₂ ≠ S₂ * S₁ := by
  let b := Module.finBasis K E
  let e := LinearMap.toMatrixAlgEquiv b
  let i0 : Fin (Module.finrank K E) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank K E) := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨e.symm (Matrix.single i0 i1 1), e.symm (Matrix.single i1 i0 1), ?_⟩
  intro hc
  have h2 := congrArg e hc
  simp only [map_mul, AlgEquiv.apply_symm_apply] at h2
  have h3 := congrFun (congrFun h2 i0) i0
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h3
  simp [Matrix.single_apply, hne.symm] at h3

theorem finrank_le_natDegree_minpoly (K V : Type) [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : Module.End K V) (hs : (minpoly K T).Separable)
    (hc : ∀ a b : Module.End K V, Commute a T → Commute b T → Commute a b) :
    Module.finrank K V ≤ (minpoly K T).natDegree := by
  classical
  set f := minpoly K T with hf
  have hmon : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  obtain ⟨hsum, -⟩ := GlobalTheory.EigSum.finrank_eigenspaces_of_separable_minpoly K V T f hmon hs
    (minpoly.aeval K T) (fun g hg => minpoly.dvd K T hg)
  have hcard : f.roots.toFinset.card = f.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)]
    exact ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
  by_contra hlt
  push_neg at hlt
  obtain ⟨μ, hμ, h2⟩ : ∃ μ ∈ f.roots.toFinset, 2 ≤ Module.finrank K (T.eigenspace μ) := by
    by_contra hno
    push_neg at hno
    have : ∑ z ∈ f.roots.toFinset, Module.finrank K (T.eigenspace z) ≤
        ∑ z ∈ f.roots.toFinset, 1 :=
      Finset.sum_le_sum fun z hz => Nat.lt_succ_iff.mp (hno z hz)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  have hroot : f.IsRoot μ := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmon.ne_zero] at hμ; exact hμ
  set q := f /ₘ (Polynomial.X - Polynomial.C μ) with hq
  have hfq : (Polynomial.X - Polynomial.C μ) * q = f :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqμ : q.eval μ ≠ 0 := by
    intro h0
    have hq' : (Polynomial.X - Polynomial.C μ) * (q /ₘ (Polynomial.X - Polynomial.C μ)) = q :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h0
    obtain ⟨q2, hq2⟩ : ∃ q2, (Polynomial.X - Polynomial.C μ) * q2 = q := ⟨_, hq'⟩
    have hu : IsUnit (Polynomial.X - Polynomial.C μ) :=
      hs.squarefree _ ⟨q2, by rw [← hfq, ← hq2]; ring⟩
    exact Polynomial.not_isUnit_X_sub_C μ hu
  set c := q.eval μ with hc_def
  set Q := Polynomial.aeval T q with hQ
  set E := T.eigenspace μ with hE
  have hTQ : ∀ v, T (Q v) = μ • Q v := by
    intro v
    have h0 : Polynomial.aeval T ((Polynomial.X - Polynomial.C μ) * q) = 0 := by
      rw [hfq]; exact minpoly.aeval K T
    have h1 := congrArg (fun g : Module.End K V => g v) h0
    simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
      LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.zero_apply] at h1
    exact sub_eq_zero.mp h1
  have hQT : ∀ v, Q (T v) = T (Q v) := by
    intro v
    have h := congrArg (Polynomial.aeval T) (mul_comm q Polynomial.X)
    simp only [map_mul, Polynomial.aeval_X] at h
    exact congrArg (fun g : Module.End K V => g v) h
  have hQE : ∀ v, Q v ∈ E := by
    intro v
    rw [hE, Module.End.mem_eigenspace_iff]
    exact hTQ v
  have hQid : ∀ u ∈ E, Q u = c • u := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [hu0]
    · exact Module.End.aeval_apply_of_hasEigenvector ⟨hu, hu0⟩
  let π : V →ₗ[K] E := Q.codRestrict E hQE
  let ι : E →ₗ[K] V := E.subtype
  have hπι : ∀ x : E, π (ι x) = c • x := by
    intro x; apply Subtype.ext; simp [π, ι, hQid x.1 x.2]
  have hπT : ∀ v, π (T v) = μ • π v := by
    intro v; apply Subtype.ext; simp [π, hQT v, hTQ v]
  have hcomm : ∀ S : Module.End K E, Commute (ι ∘ₗ S ∘ₗ π) T := by
    intro S
    apply LinearMap.ext
    intro v
    have hm : T (S (π v) : V) = μ • (S (π v) : V) := Module.End.mem_eigenspace_iff.mp (S (π v)).2
    simp only [Module.End.mul_apply, LinearMap.comp_apply, hπT v, map_smul]
    simp [ι, hm]
  obtain ⟨S₁, S₂, hS⟩ := exists_not_commute_of_two_le_finrank h2
  have hab := hc _ _ (hcomm S₁) (hcomm S₂)
  apply hS
  apply LinearMap.ext
  intro w
  have h1 := congrArg (fun g : Module.End K V => g (ι (c⁻¹ • c⁻¹ • w))) hab.eq
  simp only [Module.End.mul_apply, LinearMap.comp_apply, map_smul, hπι, smul_smul] at h1
  apply Subtype.ext
  simpa [ι, mul_inv_cancel₀ hqμ, inv_mul_cancel₀ hqμ, mul_assoc, mul_left_comm] using h1

theorem natDegree_minpoly_eq_of_commutant_comm : ∀ (K : Type) [Field K] [IsAlgClosed K] (k : ℕ)
    (N : Matrix (Fin k) (Fin k) K), (minpoly K N).Separable →
    (∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B) →
    (minpoly K N).natDegree = k := by
  intro K _ _ k N hs hc
  have hmin : minpoly K (Matrix.toLin' N) = minpoly K N := Matrix.minpoly_toLin' N
  apply le_antisymm
  · calc (minpoly K N).natDegree ≤ N.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N) (Matrix.charpoly_monic N).ne_zero
      _ = k := by rw [Matrix.charpoly_natDegree_eq_dim]; simp
  · have h := finrank_le_natDegree_minpoly K (Fin k → K) (Matrix.toLin' N) (hmin ▸ hs) ?_
    · simpa [hmin] using h
    · intro a b ha hb
      let e : Matrix (Fin k) (Fin k) K ≃ₐ[K] Module.End K (Fin k → K) := Matrix.toLinAlgEquiv'
      have hN : e.symm (Matrix.toLin' N) = N := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      have hA := ha.map e.symm
      have hB := hb.map e.symm
      rw [hN] at hA hB
      simpa only [AlgEquiv.apply_symm_apply] using (hc _ _ hA hB).map e

end GlobalTheory.RegCommutant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodular
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.PowLim.Rosati

open GlobalTheory.CechPic GlobalTheory.Mum.RosatiTens

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
  {pr : Fin r → (D'.P.A ⟶ Q.B)}

def pairQ (Q : Data R) (pr : Fin r → (D'.P.A ⟶ Q.B)) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j)

theorem cls_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) : cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (pr i) (pr j) := by
  have hC := LB.isLB_linComb Q.M.isLB (tensφ pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨w, hw⟩).trans ?_
  rw [cls_linComb Q.M.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairQ Q pr W h h := by
  rw [cls_pow w hw, pairQ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

theorem pairQ_mul (hpr : ∀ i, IsMonHom (pr i)) (W : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) :
    pairQ Q pr W (u * v) (u * v) = pairQ Q pr W u u + pairQ Q pr W v v + pairQ Q pr (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ pr i = u ≫ pr i * v ≫ pr i := fun i => by
    haveI := hpr i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (v ≫ pr i) (u ≫ pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairQ, hm, lam_mul_left Q.M.isLB hΘ, lam_mul_right Q.M.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

theorem comp_act_pr' (hl : IsLimit (Fan.mk D'.P.A pr)) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ PowLim.act pr hl m) ≫ pr i = ∏ k, (u ≫ pr k) ^ m i k := by
  rw [Category.assoc, PowLim.act_pr]
  exact (map_prod (pre (Z := Q.B) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := Q.B) u) _ _)

theorem pairQ_act_left (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M (u ≫ PowLim.act pr hl m) v = pairQ Q pr (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_left Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairQ_act_right (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M u (v ≫ PowLim.act pr hl m) = pairQ Q pr (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_right Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem rosatiAdj_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (h : IsUnit (W + W.transpose).det) (pr : Fin r → (D'.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.P.A pr))
    (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ i, IsMonHom (pr i)) → w.IsGen →
    ∀ a : TensO (symUnitOf W h), RosatiAdj D'.P.A D'.P.L (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a))) := by
  intro R _ _ Q D' r W h pr hl w hpr hw a
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := PowLim.act pr hl (TensO.mat _ a)
  let g := PowLim.act pr hl (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_pow w hw]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairQ_mul hpr, pairQ_mul hpr]
    rw [pairQ_act_left hl (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairQ_act_right hl (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by
        simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.PowLim.Rosati

theorem GlobalTheory.Mum.PFactor.nonempty_of_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
  {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → 1 ≤ r →
  ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) →
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    Nonempty (PFactor Q D'.toPre) := by
  intro R _ _ _ hR Q D' r W hpos hdet hr pr xe w hpr hlim hc hw hpsi
  let hl := hlim.some
  let s := symUnitOf W hdet
  let i₀ : Fin r := ⟨0, hr⟩
  letI := PowLim.mod xe s
  obtain ⟨w', hw', htau⟩ := GlobalTheory.T.mumfordIso_periods_factor_tensor_polarised R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi i₀
  obtain ⟨hxx, hxe, hinj, honto⟩ := PowLim.factor_latt xe s i₀
  have hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀ := by
    have h := hpos.diag_pos (i := i₀)
    have h' : (0 : ℝ) < (((W + W.transpose) i₀ i₀ : ℤ) : ℝ) := h
    exact_mod_cast h'
  exact ⟨{
    O := TensO s
    mod := PowLim.mod xe s
    o := { onB := { act := fun a => PowLim.act pr hl (TensO.mat s a)
                    hom := fun a => PowLim.act_isMonHom pr hl hpr _
                    map_one := PowLim.act_one pr hl
                    map_mul := fun a b => PowLim.act_mul pr hl _ _
                    map_add := fun a b => PowLim.act_add pr hl hpr _ _
                    rosati := GlobalTheory.Mum.PowLim.Rosati.rosatiAdj_pow R Q D'.toPre W hdet pr hl w hpr hw }
           c_lin := PowLim.c_smul Q D'.toPre pr hl xe hc s
           tau_bal := GlobalTheory.T.tensorData_periods_balanced_integralMatrices R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi }
    e := TensO.idem s i₀
    f := TensO.binv s
    inc := PowLim.inc pr hl i₀
    pr := pr i₀
    xi := PowLim.xi xe i₀
    xp := PowLim.xp xe i₀
    w := w'
    idem := TensO.idem_mul_idem s i₀
    inc_hom := PowLim.inc_isMonHom pr hl hpr i₀
    pr_hom := hpr i₀
    inc_pr := PowLim.inc_pr_self pr hl i₀
    pr_inc := PowLim.pr_inc pr hl i₀
    xp_xi := hxx
    xi_xp := hxe
    c_xi := PowLim.c_xi Q D'.toPre pr hl xe hc i₀
    inj := hinj
    onto := honto
    w_gen := hw'
    tau := htau
    alg := PowLim.alg_idem_binv s i₀ hp }⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem pre_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  intro R R₀ _ _ I hI π hπ hk C _ F hF
  have h := fun T => GlobalTheory.T.smoothAlgebra_lifts_over_square_zero_thickening R R₀ I hI π hπ hk (F.obj T) (hF T)
  choose B iB aB p hs hp hker hsm using h
  letI := iB
  letI := aB
  have hl : ∀ {T T' : C} (a : T ⟶ T'), ∃ ρ : B T →ₐ[R] B T', ∀ b, p T' (ρ b) = mp F a (p T b) :=
    fun {T T'} a => homLift R R₀ I hI π hπ hk (B T) (F.obj T) (p T) (hs T) (hp T) (hker T)
      (B T') (F.obj T') (p T') (hs T') (hp T') (hker T') (mp F a)
  exact ⟨{ B := fun T => CommAlgCat.of R (B T)
           p := p
           semi := hs
           surj := hp
           ker := hker
           smooth := hsm
           ρ := fun a => (hl a).choose
           nat := fun a b => (hl a).choose_spec b }⟩

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoprimeLatticeMultiplierStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_coprime_lattice_multiplier : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ k : ℕ, 0 < k → ∃ (m : K) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ Complex.normSq (io m) = b / modF t ∧
      ∀ u ∈ lattice c (y * (upIdele K E t)⁻¹), algebraMap K E m * u ∈ lattice c y ∧
        ((upIdele K E t : Af E) * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  first | exact @GlobalTheory.ConjApprox.approx_idele | exact GlobalTheory.ConjApprox.approx_idele | (intros; apply GlobalTheory.ConjApprox.approx_idele <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMeasureOfPublished
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasureAll

theorem oneMeasure : Hypotheses2 → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  intro hP D Tu C t0 hC i P
  refine ⟨GlobalTheory.T.level_index_bound_of_classicalTheorems hP D Tu C t0 hC i P, fun τ => GlobalTheory.T.one_le_dimAt' D i τ, fun μ 𝓕 hF =>
    ⟨GlobalTheory.T.fundamental_domain_measure_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF, GlobalTheory.T.fundamental_domain_measure_ne_top hP D Tu C t0 hC i P μ 𝓕 hF,
      GlobalTheory.T.exact_ratio_of_fundamental_domain hP D Tu C t0 hC i P μ 𝓕 hF, fun L hL =>
        ⟨fun τ => GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL τ, GlobalTheory.T.log_fundamental_domain_volume_le hP D Tu C t0 hC i P μ 𝓕 hF L hL,
          GlobalTheory.T.log_measure_ratio_le hP D Tu C t0 hC i P μ 𝓕 hF L hL⟩⟩⟩

end GlobalTheory.OneMeasureAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_relation_pullback_galois_automorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) (s s' : Fam D (Kb R) N), PhiRel D (Kb R) N p w s s' → PhiRel D (Kb R) N p₀ (frTw D τ h w) (famTw D N τ s) (famTw D N τ s') := by
  first | exact @GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw | exact GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw | (intros; apply GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleDescendsQuotientFiniteSubgroup
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareDescent

theorem descends : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A']
    [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A →
    IsAbelianScheme A' → IsAbelianScheme B → IsDual A B P → IsMonHom i → IsMonHom q → IsFinite q.left →
    Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → Triv (ev P (fst N B ≫ i) (snd N B)) →
    ∃ P' : LB (A' ⊗ B).left, P'.IsLB ∧ IsAdditive P' ∧ LBIso (ev P' (fst A B ≫ q) (snd A B)) P := by
  intro K _ _ A A' B N _ _ _ _ P i q hA hA' hB hD hi hq hfin hfl hsurj hker hN
  obtain ⟨P₀, hP₀, e⟩ := GlobalTheory.T.additive_lineBundle_descends_along_isogeny_torsor K A A' B N P i q hA hA' hB hD.isLB hD.additive hD.zero hi hq hfin hfl
    hsurj (torsor_square i q hker) hN
  have key : ∀ (Y : Over (Sp K)) (a : Y ⟶ A) (b : Y ⟶ B), evc hP₀ (a ≫ q) b = evc hD.isLB a b := by
    intro Y a b
    have c := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff (pull_isLB hP₀ _) hD.isLB).2 e)
    rw [cls_ev hP₀, pull_evc, lift_fst_assoc, lift_snd] at c
    exact c
  let φ : Fin 2 → ((A' ⊗ B).left ⟶ (A' ⊗ B).left) :=
    ![(lift (fst A' B) (snd A' B)).left, (lift (fst A' B) (1 : A' ⊗ B ⟶ B)).left]
  have hP' : (LB.LinComb P₀ φ ![1, -1]).IsLB := LB.isLB_linComb hP₀ _ _
  have ev' : ∀ (Y : Over (Sp K)) (a : Y ⟶ A') (b : Y ⟶ B), evc hP' a b = evc hP₀ a b - evc hP₀ a 1 := by
    intro Y a b
    rw [evc, cls_linComb hP₀, Fin.sum_univ_two, map_add, map_zsmul, map_zsmul, ← pull_comp, ← pull_comp]
    simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd, MonObj.comp_one, one_smul, neg_smul, evc, sub_eq_add_neg]
  have one : ∀ (Y : Over (Sp K)) (b : Y ⟶ B), evc hP₀ (1 : Y ⟶ A') b = 0 := fun Y b ↦ by
    have : (1 : Y ⟶ A) ≫ q = 1 := by simp
    rw [← this, key]
    exact hD.additive.evc_one hD.isLB b
  refine ⟨_, hP', CubeNoeth.isAdditive_of_triv_axes hA' hB hP' ?_ ?_, ?_⟩
  · rw [triv_ev_iff hP', ev', one, one, sub_self]
  · rw [triv_ev_iff hP', ev', sub_self]
  · refine (cls_eq_iff (pull_isLB hP' _) hD.isLB).1 ?_
    rw [cls_ev hP', ev', key, key, evc_one_right hD.isLB hD.zero, sub_zero, evc, lift_fst_snd, Over.id_left,
      pull_id]

end GlobalTheory.PoincareDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLemmaTruncatedDivPowerPolyOneVariableStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareLemma_truncated_divPowerPoly_oneVariable : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : Q.P →+* G) (n : ℕ), Q.IsStd δ η → IsLev δ (n + 1) → SemiHom (RingHom.id R) q → IsDPMorphism η δ' q → Function.Surjective q → J' = (Q.ext J).map q → (∀ b, q b = 0 ↔ b ∈ fil η (n + 1)) → ∀ (α : B →+* G) (h : SemiHom (RingHom.id R) α) (hd : IsDPMorphism δ δ' α), (∀ b, α b = q (algebraMap B Q.P b)) → RQ h hd := by
  first | exact @GlobalTheory.PDForm.rq_truncPoly | exact GlobalTheory.PDForm.rq_truncPoly | (intros; apply GlobalTheory.PDForm.rq_truncPoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIffStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (π : Y ⟶ X), π ≫ p = q → ∀ (y : Y) (d d' : ℕ), HasDim y d → HasDim (π y) d' → d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  first | exact @GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff | exact GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff | (intros; apply GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDetStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_neg_one_pow_card_det_sum_eq_sum_perm_det : ∀ (D : ℕ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ), ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det = ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := by
  first | exact @GlobalTheory.PolDet.polarisation_det | exact GlobalTheory.PolDet.polarisation_det | (intros; apply GlobalTheory.PolDet.polarisation_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingBoundOfDeepGoodStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_bound_of_deep_good : Hypotheses2 → Gram → DeepGood → Ring := by
  first | exact @GlobalTheory.CovTop.RingStep.ring_of | exact GlobalTheory.CovTop.RingStep.ring_of | (intros; apply GlobalTheory.CovTop.RingStep.ring_of <;> assumption)
end

