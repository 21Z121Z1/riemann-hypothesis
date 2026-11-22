import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0069
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.BilinCalc

theorem sum_antisymm {M : Type*} [AddCommGroup M] {n : ℕ} (b : Fin n → Fin n → M) (hb : ∀ i j, b i j = b j i)
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : ∀ i j, D i j + D j i = 0) :
    ∑ uv : Fin n × Fin n, D uv.1 uv.2 • b uv.1 uv.2 = 0 := by
  classical

  let E : Fin n → Fin n → ℤ := fun i j => if i < j then D i j else 0
  have hDE : ∀ i j, D i j = E i j - E j i := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [E, hij, not_lt.mpr hij.le]
    · have := hD i i
      simp [E]
      omega
    · have := hD i j
      simp [E, hij, not_lt.mpr hij.le]
      omega
  have hswap : ∑ uv : Fin n × Fin n, E uv.2 uv.1 • b uv.1 uv.2 =
      ∑ uv : Fin n × Fin n, E uv.1 uv.2 • b uv.1 uv.2 := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun uv => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hb]
  simp only [hDE, sub_smul, Finset.sum_sub_distrib, hswap, sub_self]

theorem map_prod_zpow {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    {n : ℕ} (x : Fin n → G) (c : Fin n → ℤ) : f (∏ i, x i ^ c i) = ∑ i, c i • f (x i) := by
  let φ : Additive G →+ M := AddMonoidHom.mk' (fun a => f a.toMul) fun a a' => hf _ _
  have hφ : ∀ g : G, f g = φ (Additive.ofMul g) := fun _ => rfl
  rw [hφ, ofMul_prod, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofMul_zpow, map_zsmul, ← hφ]

theorem sum_subst {G M : Type*} [CommGroup G] [AddCommGroup M] (B : G → G → M)
    (hB : ∀ x x' y, B (x * x') y = B x y + B x' y) (hs : ∀ x y, B x y = B y x) {n m : ℕ} (x : Fin n → G)
    (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ)
    (h : W' + W'.transpose = c.transpose * (W + W.transpose) * c) :
    ∑ uv : Fin n × Fin n, W' uv.1 uv.2 • B (x uv.1) (x uv.2) =
      ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) := by
  classical
  have hL : ∀ (y : G) (k : Fin n → ℤ), B (∏ i, x i ^ k i) y = ∑ i, k i • B (x i) y :=
    fun y k => map_prod_zpow (fun g => B g y) (fun g g' => hB g g' y) x k
  have hR : ∀ (z : G) (k : Fin n → ℤ), B z (∏ i, x i ^ k i) = ∑ i, k i • B z (x i) :=
    fun z k => map_prod_zpow (fun g => B z g) (fun g g' => by rw [hs z, hB, hs g, hs g']) x k

  have hV : ∀ i j, ∑ a : Fin m, ∑ a' : Fin m, W a a' * (c a i * c a' j) = (c.transpose * W * c) i j := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hrhs : ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) =
      ∑ ij : Fin n × Fin n, (c.transpose * W * c) ij.1 ij.2 • B (x ij.1) (x ij.2) := by
    simp only [hL, hR, Finset.smul_sum, smul_smul, Fintype.sum_prod_type, ← hV, Finset.sum_smul]
    calc _ = ∑ a : Fin m, ∑ i : Fin n, ∑ j : Fin n, ∑ a' : Fin m,
          (W a a' * (c a i * c a' j)) • B (x i) (x j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hrhs, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  refine sum_antisymm (fun i j => B (x i) (x j)) (fun i j => hs _ _) (W' - c.transpose * W * c) fun i j => ?_
  have hij := congrFun (congrFun h i) j
  have ht : (c.transpose * W * c).transpose = c.transpose * W.transpose * c := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hji := congrFun (congrFun ht i) j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_add, Matrix.add_mul] at hij hji
  simp only [Matrix.sub_apply]
  linarith

open GlobalTheory.CechPic in

theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Pb : LB (G2 A).left), Pb.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso Pb (Pb.pull (lift (snd A A) (fst A A)).left) → ∀ (T : Over S) (n m : ℕ) (x : Fin n → (T ⟶ A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ), W' + W'.transpose = c.transpose * (W + W.transpose) * c → LBIso (LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (x uv.1) (x uv.2)).left) (fun uv => W' uv.1 uv.2)) (LB.LinComb Pb (K := Fin m × Fin m) (fun uv => (lift (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i)).left) (fun uv => W uv.1 uv.2)) := by
  intro S A _ _ Pb hPb hbi hsym T n m x W W' c h
  classical

  let β : (T ⟶ A) → (T ⟶ A) → Pic T.left := fun u v => pull (lift u v).left (cls Pb hPb)
  have hadd : ∀ u u' v : T ⟶ A, β (u * u') v = β u v + β u' v := by
    intro u u' v
    obtain ⟨t, ht⟩ := (hbi T u u' v).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hPb _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hPb] at e
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul] at e
    simp only [β]
    rw [← sub_eq_zero, ← e]
    abel
  have hsw : ∀ u v : T ⟶ A, β u v = β v u := by
    intro u v
    have e : cls Pb hPb = cls _ (pull_isLB hPb _) := (cls_eq_iff hPb (pull_isLB hPb _)).2 hsym
    rw [cls_pull hPb] at e
    simp only [β]
    conv_lhs => rw [e, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  refine (cls_eq_iff (LB.isLB_linComb hPb _ _) (LB.isLB_linComb hPb _ _)).1 ?_
  rw [cls_linComb hPb, cls_linComb hPb]
  exact sum_subst β hadd hsw x W W' c h

end GlobalTheory.BilinCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MatrixIntertwinesAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS

private lemma constFn_sub' {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (a b : K) :
    constFn q O (a - b) = constFn q O a - constFn q O b := by
  unfold constFn
  simp only [map_sub]

private lemma constFn_mul_moduli {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (a b : K) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  unfold constFn
  simp only [map_mul]

private lemma constFn_sum {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) {n : ℕ}
    (f : Fin n → K) : constFn q O (∑ k, f k) = ∑ k, constFn q O (f k) := by
  unfold constFn
  simp only [map_sum]

private lemma sum_sub_sum_mul_eq_sub_sub_sum {R : Type*} [CommRing R] {n : ℕ} (A B u v : Fin n → R) (M N : Fin n → Fin n → R) :
    ∑ a, (∑ b, A b * M b a - ∑ b, B b * N a b) * v a =
      (∑ a, A a * u a - ∑ a, B a * ∑ b, N b a * v b) - ∑ a, A a * (u a - ∑ b, M a b * v b) := by
  have h1 : ∑ a, ∑ b, A b * M b a * v a = ∑ a, ∑ b, A a * (M a b * v b) := by
    rw [Finset.sum_comm]; simp only [_root_.mul_assoc]
  have h2 : ∑ a, ∑ b, B b * N a b * v a = ∑ a, ∑ b, B a * (N b a * v b) := by
    rw [Finset.sum_comm]; simp only [_root_.mul_assoc]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_sub, Finset.mul_sum]
  rw [h1, h2]
  abel

theorem lc_row_mul_sub {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} (q : Y ⟶ Sp K) {g : ℕ}
    (F Θ F' : Matrix (Fin g) (Fin g) K) (θ φ : Fin g → C1 U) (x : Fin g) :
    lc q ((F * Θ - Θ * F'.transpose) x) φ =
      (lc q (F x) θ - lc q (Θ x) (fun c => lc q (fun y => F' y c) φ)) -
        lc q (F x) (fun b => θ b - lc q (Θ b) φ) := by
  funext i j
  simp only [lc, Pi.sub_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    constFn_sub', constFn_sum, constFn_mul_moduli]
  exact sum_sub_sum_mul_eq_sub_sub_sum (fun b => constFn q (U i ⊓ U j) (F x b)) (fun b => constFn q (U i ⊓ U j) (Θ x b))
    (fun b => θ b i j) (fun b => φ b i j) (fun a b => constFn q (U i ⊓ U j) (Θ a b))
    (fun a b => constFn q (U i ⊓ U j) (F' a b))

theorem matrix_intertwines_adjoint : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∀ (Θ : Matrix (Fin g) (Fin g) K) (f : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), (∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ)) → IsMonHom f₀ → IsMonHom f₀' → f₀.left ≫ m = m ≫ f.left → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → F * Θ = Θ * F'.transpose := by
  intro K _ P₀ g v dd hv hdd R _ x₀ P m L _ D d θ φ hpb hL hLaff hLB hKS hφ Θ f f₀ f₀' F F' hcob hf₀ hf₀' hfm hcube hF hF'
  have hsm : Smooth P₀.A.hom := @IsAbelianScheme.smooth _ P₀.A P₀.grp P₀.isAb
  have hA := GlobalTheory.T.kodairaSpencerClass_cohomologous_along_endomorphism K P₀.A g v dd hsm hv hdd R x₀ P.A.left P.A.hom m hpb.1 L.ι L.U D d θ f.left f₀ F hKS hf₀
    (Over.w f) hfm hF
  have hB := GlobalTheory.T.cohomology_logDerivative_adjoint_endomorphisms K P₀ g v dd hv hdd P.A.left m L φ f₀ f₀' F' hL hLB hφ hf₀ hf₀' hcube hF'
  have hI := (GlobalTheory.T.logDerivative_principalPolarisation_independent K P₀ g v dd hv hdd P.A.left m L hL hLB).2 φ hφ |>.2
  have hcov : ⨆ i, m ⁻¹ᵁ L.U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hL.cover]; rfl
  have hrow : ∀ x, (F * Θ - Θ * F'.transpose) x = 0 := by
    intro x
    apply hI
    rw [lc_row_mul_sub]
    refine IsCob.sub (Cohom.isCob_sub f₀.left hcov (hA x)
      (cohom_lc P₀.A.hom f₀.left (Over.w f₀) (Θ x) _ φ hB) (hcob x)) ?_
    exact isCob_lc P₀.A.hom (F x) _ hcob
  rw [← sub_eq_zero]
  ext x y
  exact congrFun (hrow x) y

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjMapOfIsHeckeIsog
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

theorem exists_torsion_lift {Q Q' : Type} [CommGroup Q] [CommGroup Q'] (ψ : Q →* Q') (hs : Function.Surjective ψ)
    {q n : ℕ} (hq : ∀ x, ψ x = 1 → x ^ q = 1) (hn : 0 < n) (hc : n.Coprime q) (y : Q') (hy : y ^ n = 1) :
    ∃ x, x ^ n = 1 ∧ ψ x = y := by
  obtain ⟨u, rfl⟩ := hs y
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hc.symm hn.ne'
  refine ⟨u ^ (q * r), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_mul, hq _ ((map_pow _ _ _).trans hy), one_pow]
  · rw [map_pow, pow_eq_pow_of_modEq (show q * r ≡ 1 [MOD n] from hr) hy, pow_one]

theorem objMap_of_isHeckeIsog [IsAlgClosed k] [CharZero k] (hL : Out.Laws)
    (hfacts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L)
    (hDet : ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)))
    {o o₁ o₂ : Obj D l b s} {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ l.M') {C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)}
    (hC : ∀ x ∈ C, x ^ p ^ 2 = 1) {ψ₁ : o.t.G ⟶ o₁.t.G} {ψ₂ : o.t.G ⟶ o₂.t.G} (h₁ : IsHeckeIsog o o₁ p C ψ₁)
    [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left] (h₂ : IsHeckeIsog o o₂ p C ψ₂) :
    Nonempty (ObjMap o₁ o₂ (𝟙 _)) := by
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁
  obtain ⟨hom₂, lin₂, sur₂, ker₂, weil₂, lev₂⟩ := h₂
  obtain ⟨hab, hdim, -, -⟩ := hfacts E H D l B b _ s o
  obtain ⟨hab₁, hdim₁, -, -⟩ := hfacts E H D l B b _ s o₁
  obtain ⟨hab₂, hdim₂, -, -⟩ := hfacts E H D l B b _ s o₂
  let P := polOf o.t o.proper o.ample o.ktriv hdim
  let P₁ := polOf o₁.t o₁.proper o₁.ample o₁.ktriv hdim₁
  let P₂ := polOf o₂.t o₂.proper o₂.ample o₂.ktriv hdim₂
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, hα⟩ := exists_fac hab.smooth ψ₁ ψ₂ fun x hx => (ker₂ x).2 ((ker₁ x).1 hx)
  have homα : IsMonHom α := hL.rigidity _ _ _ hab₁ hab₂ α (by
    rw [← IsMonHom.one_hom ψ₁, Category.assoc, hα, IsMonHom.one_hom])
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  let ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  have hlam : LBIso (abelian₂ o₁.t.G (lbPow o₁.t.PP.L 1)) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    hDet k P₁ P₂ α p 1 homα hp inferInstance fun n x y c hn hc hx hy h => by
      have lift := exists_torsion_lift ρ sur₁ (fun x hx => hC x ((ker₁ x).1 hx)) hn (hc.pow_right 2)
      obtain ⟨x₀, tx, ex⟩ := lift x hx
      obtain ⟨y₀, ty, ey⟩ := lift y hy
      obtain rfl : x₀ ≫ ψ₁ = x := ex
      obtain rfl : y₀ ≫ ψ₁ = y := ey
      obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P n _).1 x₀ y₀ tx ty
      obtain ⟨c₀, rfl⟩ := (unitOn_bijective k).2 c₀
      have e : c = c₀ ^ p ^ 2 := (unitOn_bijective k).1
        (((hL.weil _ P₁ n _).1 _ _ hx hy).unique h (weil₁ n x₀ y₀ c₀ hc hc₀))
      have w := weil₂ n x₀ y₀ c₀ hc hc₀
      rw [← hα, ← Category.assoc, ← Category.assoc, ← e] at w
      rw [pow_one]
      exact w
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have := mono_of_kTriv α o₁.t.PP.isLB o₂.t.PP.isLB hiso o₁.ktriv
  have : IsIso α := isIso_of_mono α hab₂.smooth fun y => by
    obtain ⟨x, rfl⟩ := sur₂ y
    exact ⟨x ≫ ψ₁, by rw [Category.assoc, hα]⟩
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso hL.globalFns hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

end GlobalTheory.HeckePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem relAmple_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.RelAmple (G i) (M i)) → Out.RelAmple A L := by
  intro S I U A _ G _ ψ hU hψ L M hL hM hiso hA _ hamp
  have : IsProper A.hom := hA.proper
  refine GlobalTheory.AmpleLocal.relAmple_of_locally S A L hL inferInstance inferInstance fun s => ?_
  obtain ⟨i, hi⟩ := exists_mem hU s
  obtain ⟨V, hV, hs, hle⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := U i) (x := s) hi
  have hle' : V ≤ U i := hle
  refine ⟨V, hs, ?_⟩
  have h := (hψ i).1
  have hf : S.homOfLE hle' ≫ (U i).ι = V.ι := S.homOfLE_ι hle'
  have sq : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = ((A.hom ∣_ V) ≫ S.homOfLE hle') ≫ (U i).ι := by
    rw [Category.assoc, hf, morphismRestrict_ι]
  let φ : (A.hom ⁻¹ᵁ V).toScheme ⟶ (G i).left := h.lift _ _ sq
  have hφ : φ ≫ ψ i = (A.hom ⁻¹ᵁ V).ι := h.lift_fst _ _ _
  have H : IsPullback φ (A.hom ∣_ V) (G i).hom (S.homOfLE hle') := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hφ, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  obtain ⟨w, hw⟩ : LBIso (L.pull (A.hom ⁻¹ᵁ V).ι) ((M i).pull φ) :=
    LBIso.chartPull (chartPullSame L (fun _ : PUnit => (A.hom ⁻¹ᵁ V).ι) (fun _ => ψ i) (fun _ => 1) φ fun _ => hφ.symm)
      (chartPullPull (M i) φ φ rfl) (hiso i).symm
  refine relAmple_pull (A' := Over.mk (A.hom ∣_ V)) H (hM i) (pull_isLB hL _) ((isGen_iff w).1 hw) ((U i).ι ⁻¹ᵁ V)
    (hV.preimage_of_isOpenImmersion _ (by simpa using hle')) (fun y => ?_) (hamp i)
  show (U i).ι (S.homOfLE hle' y) ∈ V
  rw [← Scheme.Hom.comp_apply, hf]
  exact y.2

end GlobalTheory.CoverGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppOfPullbackSnd
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RigidLocal

open GlobalTheory.CechPic

private theorem surjective_app_of_eq_of_surjective_comp_injective {X S : Scheme.{0}} (f : X ⟶ S) {W V : S.Opens} (e : W = V)
    {R : CommRingCat} (g : Γ(X, f ⁻¹ᵁ W) ⟶ R)
    (h : Function.Surjective (f.app W ≫ g).hom) (hg : Function.Injective g.hom) :
    Function.Surjective (f.app V).hom := by
  subst e
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact h.of_comp_left hg

theorem surjective_app_of_pullback_snd {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : Function.Surjective (pullback.snd f V.ι).appTop.hom) : Function.Surjective (f.app V).hom := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.coe_comp] at h
  have hi : IsIso (pullbackRestrictIsoRestrict f V).hom.appTop :=
    inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))
  have h2 : Function.Surjective (f ∣_ V).appTop.hom :=
    h.of_comp_left (ConcreteCategory.bijective_of_isIso (pullbackRestrictIsoRestrict f V).hom.appTop).1
  rw [morphismRestrict_appTop] at h2
  refine surjective_app_of_eq_of_surjective_comp_injective f V.ι_image_top _ h2 ?_
  exact (ConcreteCategory.bijective_of_isIso
    (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f V ⊤)).op).hom).1

theorem eSec_comp {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] {φ : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (𝟙 S) φ) : eSec A ≫ φ = eSec A' :=
  (GlobalTheory.PolBaseChange.eSec_comm h).trans (Category.id_comp _)

theorem lbIso_of_local : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (φ : A.left ⟶ A'.left), IsAbelianScheme A → L.IsLB → L'.IsLB → Out.Rigidified A L → Out.Rigidified A' L' → IsGrpPullback A A' (𝟙 S) φ → (∀ p : S, ∃ (V B : Scheme.{0}) (x : V ⟶ S) (q : B ⟶ V) (a : B ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsPullback a q A.hom x ∧ LBIso (L.pull a) (L'.pull (a ≫ φ))) → LBIso L (L'.pull φ) := by
  intro hG S A A' _ _ L L' φ hA hL hL' hR hR' hφ hloc
  have hM : (L'.pull φ).IsLB := LB.isLB_pull hL' φ
  have hN : (LB.div L (L'.pull φ)).IsLB := LB.isLB_div hL hM

  have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ A.left),
      (∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull g), t.IsGen) ↔
        CechPic.pull g (CechPic.cls L hL) = CechPic.pull g (CechPic.cls _ hM) := by
    intro Y g
    rw [← cls_eq_zero_iff (LB.isLB_pull hN g), cls_pull hN g (LB.isLB_pull hN g), cls_div hL hM hN,
      map_sub, sub_eq_zero]

  have hsec : ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (eSec A)), t.IsGen := by
    rw [key]
    have h1 : CechPic.pull (eSec A) (CechPic.cls L hL) = 0 := by
      rw [← cls_pull hL (eSec A) (LB.isLB_pull hL _)]
      exact (cls_eq_zero_iff _).2 hR
    have h2 : CechPic.pull (eSec A') (CechPic.cls L' hL') = 0 := by
      rw [← cls_pull hL' (eSec A') (LB.isLB_pull hL' _)]
      exact (cls_eq_zero_iff _).2 hR'
    rw [h1, cls_pull hL' φ hM, ← pull_comp, eSec_comp hφ, h2]

  have hloc' : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (A.hom ⁻¹ᵁ U).ι), t.IsGen := by
    intro s
    obtain ⟨V, B, x, q, a, hx, hs, hpb, hiso⟩ := hloc s
    refine ⟨x.opensRange, hs, ?_⟩
    rw [key]
    have w : (A.hom ⁻¹ᵁ x.opensRange).ι ≫ A.hom = ((A.hom ∣_ x.opensRange) ≫ x.isoOpensRange.inv) ≫ x := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
    obtain ⟨e, he⟩ : ∃ e, e ≫ a = (A.hom ⁻¹ᵁ x.opensRange).ι := ⟨hpb.lift _ _ w, hpb.lift_fst _ _ w⟩
    have ha : CechPic.pull a (CechPic.cls L hL) = CechPic.pull a (CechPic.cls _ hM) := by
      have h := (cls_eq_iff (LB.isLB_pull hL a) (LB.isLB_pull hL' (a ≫ φ))).2 hiso
      rw [cls_pull hL a, cls_pull hL' (a ≫ φ), pull_comp] at h
      rw [h, cls_pull hL' φ hM]
    rw [← he, pull_comp, pull_comp, ha]
  have hσ : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    exact (Over.w _).trans rfl
  have hsurj : ∀ U : S.Opens, Function.Surjective (A.hom.app U).hom := fun U =>
    surjective_app_of_pullback_snd A.hom U (surj_snd hG hA (Over.mk U.ι))
  obtain ⟨t, ht⟩ := exists_gen_of_local_of_section A.left S A.hom (eSec A) _ hN hσ hsurj hloc' hsec
  exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 ((cls_div hL hM hN).symm.trans ((cls_eq_zero_iff hN).2 ⟨t, ht⟩)))

end GlobalTheory.RigidLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem kTriv_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.KTriv (G i) (M i)) → Out.KTriv A L := by
  intro S I U A _ G _ ψ hU hG L M hL hM hLM hA hGA hK
  rw [GlobalTheory.UU.kTriv_iff_forall]
  intro T x hx
  apply over_ext hU
  intro i T' r
  obtain ⟨y, hy⟩ := exists_lift (hG i).1 (r ≫ x)
  have hpush : pushPt (hG i).1.w y = r ≫ x := by
    ext1
    exact hy.symm
  have hyK : GlobalTheory.UU.InK (G i) (M i) y :=
    GlobalTheory.UU.inK_of_push (hG i) hL (hM i) (hLM i) y (hpush ▸ hx.comp r)
  have hy1 : y = 1 := (GlobalTheory.UU.kTriv_iff_forall.1 (hK i)) T' y hyK
  have hsq : (r ≫ x) * (r ≫ x) = r ≫ x := by
    ext1
    rw [((hG i).2 T' y y (r ≫ x) (r ≫ x) hy hy), hy, hy1, _root_.mul_one]
  have h1 : r ≫ x = 1 := by simpa using hsq
  rw [h1]
  simp

end GlobalTheory.CoverGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TmapOfGlies
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem tmap_of_glies : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o) (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → GLies A act Q (y ≫ c) u ψ → LBIso u.L (L.pull ψ) → (∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁) → TMap u t₁ y := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ u ψ hL ⟨h₁, h₄, _⟩ h₂ ⟨k₁, k₄, _⟩ k₂ k₃
  have hp := h₁.1
  obtain ⟨F, hF, hw⟩ : ∃ F : u.A.left ⟶ t₁.A.left, F ≫ ψ₁ = ψ ∧ F ≫ t₁.A.hom = u.A.hom ≫ y :=
    ⟨hp.lift ψ (u.A.hom ≫ y) (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst hF
  refine ⟨F, h₁.cancel k₁ hw, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans u.isLB (pull_isLB hL _) (pull_isLB t₁.isLB _) k₂ (lbIso_pull_comp h₂ F).symm
  · apply hp.hom_ext
    · rw [Category.assoc, k₃, Category.assoc]
    · have a₁ : (u.pt i).left ≫ u.A.hom = 𝟙 S₂ := Over.w (u.pt i)
      have a₂ : (t₁.pt i).left ≫ t₁.A.hom = 𝟙 S₁ := Over.w (t₁.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

end GlobalTheory.ZM.NearBuild
end
end

