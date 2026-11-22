import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0966
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionKernelEqBaseOnRealUnitaryPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
namespace GlobalTheory.RealTwistKer

open scoped ComplexConjugate

theorem exists_idele_all {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    {z : D.what₂.Tau → ℂ} (hz : ∀ τ, z τ ≠ 0) :
    ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ ∀ τ, θ τ (infPart D (y : AE D)) = z τ := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let a : (D.what₂.Tau → ℂ) → AE D := fun w => 1 + σ (w - 1)
  have a1 : ∀ w, finPart D (a w) = 1 := fun w => by
    simp only [a]
    rw [RingHom.map_add, hσ.fin, RingHom.map_one, add_zero]
  have a3 : ∀ w τ, θ τ (infPart D (a w)) = w τ := fun w τ => by
    simp only [a]
    rw [RingHom.map_add, RingHom.map_add, hσ.comp, RingHom.map_one, RingHom.map_one, Pi.sub_apply, Pi.one_apply]
    ring
  have m : a z * a z⁻¹ = 1 := by
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
    · rw [RingHom.map_sub, RingHom.map_mul, a1, a1, RingHom.map_one, mul_one, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, RingHom.map_one,
        a3, a3, Pi.inv_apply, mul_inv_cancel₀ (hz τ), sub_self]
  exact ⟨⟨a z, a z⁻¹, m, by rw [mul_comm, m]⟩, a1 z, a3 z⟩

set_option maxHeartbeats 800000 in

theorem exists_isDetRoot_pow {D : D7} (V : HSp D) {u : GA D V} (hu : u ∈ GinfC V) (n : ℕ) (hn : 0 < n) :
    ∃ y : (AE D)ˣ, IsDetRoot V u (y ^ n) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨x0, hx0⟩ := (GlobalTheory.Member.isDetRoot_laws D V).1 u
  have hcm := GlobalTheory.Mem.VolExists.isCMExt D.sp.cm
  have einf : ∀ w : AE D, infPart D (sigR (AF D.host.F) D.sp.cm.sig w) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D w) :=
    fun w => GlobalTheory.DetCharArch.map_conj _ _ _
  have efin : ∀ w : AE D, finPart D (sigR (AF D.host.F) D.sp.cm.sig w) = sigR (Af D.host.F) D.sp.cm.sig (finPart D w) :=
    fun w => GlobalTheory.DetCharArch.map_conj _ _ _
  set dt : AE D := (matHom V u).1.det with hdt
  have hfd : finPart D dt = 1 := by
    have h1 : (finHom V u).1.det = finPart D dt := ((finPart D).map_det _).symm
    have h2 : finHom V u = 1 := hu
    rw [← h1, h2]
    simp

  have hd1 : ∀ τ, ‖θ τ (infPart D dt)‖ = 1 := fun τ => by
    have hz : θ τ (infPart D (x0 : AE D)) ≠ 0 := (x0.isUnit.map ((θ τ).comp (infPart D))).ne_zero
    have k : θ τ (infPart D (x0 : AE D)) = θ τ (infPart D (dt * sigR (AF D.host.F) D.sp.cm.sig (x0 : AE D))) :=
      congrArg (fun w => θ τ (infPart D w)) hx0
    rw [RingHom.map_mul, RingHom.map_mul, einf, GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ τ)] at k
    have k2 := congrArg norm k
    rw [norm_mul, Complex.norm_conj] at k2
    have hn0 : ‖θ τ (infPart D (x0 : AE D))‖ ≠ 0 := norm_ne_zero_iff.2 hz
    exact (mul_left_eq_self₀.1 k2.symm).resolve_right hn0
  choose s hs using fun τ => IsAlgClosed.exists_pow_nat_eq (θ τ (infPart D dt)) (by omega : 0 < 2 * n)
  have hs1 : ∀ τ, ‖s τ‖ = 1 := fun τ => by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega : 2 * n ≠ 0)).1 ?_
    rw [← norm_pow, hs, hd1]
  have hs0 : ∀ τ, s τ ≠ 0 := fun τ => norm_ne_zero_iff.1 (by rw [hs1]; exact one_ne_zero)
  obtain ⟨y, hy1, hy2⟩ := exists_idele_all hθ hs0
  refine ⟨y, ?_⟩
  show ((y ^ n : (AE D)ˣ) : AE D) = dt * sigR (AF D.host.F) D.sp.cm.sig ((y ^ n : (AE D)ˣ) : AE D)
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, efin, Units.val_pow_eq_pow_val, RingHom.map_pow, hy1, one_pow, hfd,
      RingHom.map_one, mul_one, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_mul, einf,
      GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ τ), Units.val_pow_eq_pow_val, RingHom.map_pow, RingHom.map_pow, hy2,
      ← hs τ, map_pow]
    have hc : conj (s τ) * s τ = 1 := by
      rw [mul_comm, Complex.mul_conj', hs1]; simp
    rw [sub_eq_zero, two_mul, pow_add, mul_assoc, ← mul_pow (s τ) (conj (s τ)), mul_comm (s τ) (conj (s τ)), hc, one_pow, mul_one]

end GlobalTheory.RealTwistKer

namespace GlobalTheory.RealTwistKer

theorem weil_kernel_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ u ∈ GinfC (Vc D i), ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ω (u, 1) f = R.ωP i A.μ0 (u, 1) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK u hu f hf
  obtain ⟨n, hn, hξn⟩ := hK.fin
  obtain ⟨y, hy⟩ := exists_isDetRoot_pow (Vc D i) hu n hn
  have h := GlobalTheory.TwistFactorProof.weil_ratio (GlobalTheory.T.weilDatum_unique_on_thetaFunctions D) (GlobalTheory.WeilChange.exists_weilDatum_twist D)
    (hR.thP.ωP i A.μ0) hK.weil hy (GlobalTheory.TwistFactorProof.isDetRoot_one _) hf
  have hc : ChrEq (χ ^ n) 1 := by
    have := GlobalTheory.ConjTwist.BaseInhab.chrEq_pow hK.chr n hn
    rwa [show ξ ^ n = 1 from hξn] at this
  have e1 : χ (y ^ n) = 1 := by
    rw [map_pow, ← MonoidHom.pow_apply]
    exact GlobalTheory.ChrEqUnique.eq_one_of_chrEq hc y
  have e2 : R.xi A.μ0 (y ^ n) = 1 :=
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0) _
  have e3 : ∀ j, R.toLevCh.mu A.μ0 j (y ^ n) = R.mu0 j (y ^ n) * R.xi A.μ0 (y ^ n) := fun j => rfl
  rw [h]
  convert one_smul ℂ (R.ωP i A.μ0 (u, 1) f)
  show (((_ * _ : Circle) : ℂ)) = 1
  simp only [Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Lift.tup, MonoidHom.mul_apply, e3, e1, e2, map_one, mul_one, inv_one,
    mul_inv_cancel]
  simp

end GlobalTheory.RealTwistKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRootsUnity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdPairing

open GlobalTheory.CechPic GlobalTheory.DiagPairing

section Theta

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (A ⊗ A).left} (hP : P.IsLB)
  (hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y)
  (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y')

include hB in
theorem pc_one_left {T : Over S} (y : T ⟶ A) : pc hP (1 : T ⟶ A) y = 0 := by
  have := hB T 1 1 y
  rwa [_root_.mul_one, left_eq_add] at this

include hB' in
theorem pc_one_right {T : Over S} (x : T ⟶ A) : pc hP x (1 : T ⟶ A) = 0 := by
  have := hB' T x 1 1
  rwa [_root_.mul_one, left_eq_add] at this

include hB hB' in

theorem exists_theta_prod {k : ℕ} {T : Over S} (X : T ⟶ G2 A) (hX : X ^ k = 1) :
    ∃ θ : Out.ThetaGrp (G2 A) P k T, θ.pt = X := by
  have e : ∀ g : T ⊗ G2 A ⟶ G2 A, pull g.left (cls P hP) = pc hP (g ≫ fst A A) (g ≫ snd A A) := fun g => by
    unfold pc
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have tr : Out.translPt (G2 A) X = (fst T (G2 A) ≫ X) * snd T (G2 A) := rfl
  have h₁ : (fst T (G2 A) ≫ X ≫ fst A A) ^ k = 1 := by
    rw [← Category.assoc, ← pow_comp, ← comp_pow, hX, MonObj.comp_one, MonObj.one_comp]
  have h₂ : (fst T (G2 A) ≫ X ≫ snd A A) ^ k = 1 := by
    rw [← Category.assoc, ← pow_comp, ← comp_pow, hX, MonObj.comp_one, MonObj.one_comp]
  have z₁ : ∀ y, k • pc hP (fst T (G2 A) ≫ X ≫ fst A A) y = 0 := fun y => by
    rw [← pc_pow_left hP hB, h₁, pc_one_left hP hB]
  have z₂ : ∀ x, k • pc hP x (fst T (G2 A) ≫ X ≫ snd A A) = 0 := fun x => by
    rw [← pc_pow_right hP hB', h₂, pc_one_right hP hB']
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB (G2 A) P k X), t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_two]
    show (k : ℤ) • pull (snd T (G2 A)).left _ + (-(k : ℤ)) • pull (Out.translPt (G2 A) X).left _ = 0
    rw [e, e, tr, mul_comp, mul_comp, Category.assoc, Category.assoc, hB, hB', hB']
    simp only [natCast_zsmul, neg_smul, smul_add, z₁, z₂]
    abel
  exact ⟨⟨X, t, ht⟩, rfl⟩

end Theta

theorem exists_weilIs_prod_root : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (k : ℕ), 0 < k → ∀ (T : Over S) (X Y : T ⟶ G2 A), X ^ k = 1 → Y ^ k = 1 →
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ k = 1 ∧ Out.WeilIs (G2 A) P k X Y c := by
  intro S A _ _ hA P hP rig₁ rig₂ hamp k hk T X Y hX hY
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP rig₁ rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP rig₁ rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ Z : T ⟶ G2 A, Z ^ k = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp (G2 A) P k (Out.overRes V), θ.pt = Out.overResι V ≫ Z := fun Z hZ p => by
    obtain ⟨θ, hθ⟩ := exists_theta_prod hP hB hB' (k := k) (Out.overResι ⊤ ≫ Z)
      (by rw [← MonObj.comp_pow, hZ, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hAA hP (lifts X hX) (lifts Y hY)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hAA hP (lifts 1 (one_pow k)) (lifts Y hY)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG hAA hP h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs (G2 A) P k (X ^ (m + 1)) Y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ X (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP ih hc₀
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hX] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG hAA hP hp (e₁' ▸ hc₁), hc₀⟩

end GlobalTheory.ProdPairing
end
end

