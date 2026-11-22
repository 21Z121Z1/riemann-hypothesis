import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Interchange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.PolTensBimult

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TensCub

theorem interchange {U X : Type} [CommGroup U] [AddCommGroup X] (t : X → X → U) (hs : ∀ u v, t u v = t v u)
    (hc : ∀ u u' v, t u' v * (t (u + u') v)⁻¹ * t u v = t v u' * (t (u + v) u')⁻¹ * t u u') (x x' y y' : X) :
    t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹ := by
  have h₁ := hc y y' (x + x')
  have h₂ := hc x' y' (x + y)
  have h₃ := hc x x' y
  rw [hs (y + y'), hs y' (x + x'), hs y (x + x')] at h₁
  rw [hs (x' + y'), hs y' (x + y), hs x' (x + y), show x' + (x + y) = y + (x + x') by abel] at h₂
  rw [hs y x'] at h₃
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  have k₃ := congrArg Additive.ofMul h₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at k₁ k₂ k₃ ⊢
  rw [← sub_eq_zero] at k₁ k₂ k₃ ⊢
  have k := congrArg₂ (· - ·) (congrArg₂ (· - ·) k₂ k₁) k₃
  simp only [sub_zero] at k
  rw [← k]
  abel

theorem alg {U X X' : Type} [CommGroup U] [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (e : X' ≃+ (Fin r → X)) (O ψ' : X' → U) (τ' : X' → X' → U) (t : X → X → U) (c' rig' : U)
    (a a' b : X') (h0 : t 0 0 = 1)
    (ht : ∀ x x' y y', t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹)
    (hψ : ∀ u, ψ' u = O u * ∏ i, ∏ j, t (e u i) (e u j) ^ W i j)
    (hτ : ∀ u v, τ' u v = ψ' (u + v) * (ψ' u)⁻¹ * (ψ' v)⁻¹ * rig'⁻¹) (hr : ψ' 0 * rig' = 1)
    (hc : c' * (O (a + a' + b) * (O (a + a'))⁻¹ * (O (a + b))⁻¹ * (O (a' + b))⁻¹ * O a * O a' * O b * (O 0)⁻¹) =
      ∏ k : (Fin r × Fin r) × Fin 4,
        (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          t (![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2 + ![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2)
            (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2))⁻¹) ^ tensε W k) :
    τ' (a + a') b * c' = τ' a b * τ' a' b := by
  have hr' : rig'⁻¹ = ψ' 0 := (eq_inv_of_mul_eq_one_right hr).symm ▸ inv_inv _
  have hτ' : ∀ u v, τ' u v = O (u + v) * (O u)⁻¹ * (O v)⁻¹ * O 0 *
      ∏ i, ∏ j, (t (e u i + e u j) (e v i + e v j) * (t (e u i) (e v i))⁻¹ * (t (e u j) (e v j))⁻¹) ^ W i j := by
    intro u v
    rw [hτ, hr']
    simp only [hψ, map_add, Pi.add_apply, map_zero, Pi.zero_apply, h0, one_zpow, Finset.prod_const_one, ← ht (e u _) (e v _)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, ofMul_one]
    abel
  rw [eq_mul_inv_of_mul_eq hc, hτ', hτ', hτ']
  simp only [Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, Pi.add_apply,
    add_zero, h0]
  have e1 : ∀ i j, e a i + e a j + (e a' i + e a' j) = e a i + e a' i + (e a j + e a' j) := fun i j => by abel
  simp only [e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, _root_.mul_one, mul_neg, neg_smul, ofMul_one, smul_zero, Finset.sum_const_zero]
  abel

theorem cubV_prod (hG : GlobalFnsSt) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) {M' : RigLB A} {M : RigLB B} (c' : CubicalStr A M') (c : CubicalStr B M) {N : Type} [Fintype N]
    (P : N → (A ⟶ B)) (hP : ∀ k, IsMonHom (P k)) (φ : N → (A.left ⟶ B.left)) (hφ : ∀ k, (P k).left = φ k) (n : N → ℤ)
    (w : LB.Iso M'.L (LB.LinComb M.L φ n)) (hw : w.IsGen) {T : Over S} (z : T.left) (J J') (hJ : Good M.L z J)
    (hJ' : Good M'.L z J') (x x' y : T ⟶ A) (om : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ)
    (hom : om = fun p => bwg w p.left z (fun k => J (p.left ≫ φ k)) (J' p.left)) :
    cubV c' z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y *
      (om 1)⁻¹) = ∏ k, cubV c z J (x ≫ P k) (x' ≫ P k) (y ≫ P k) ^ n k := by
  subst hom
  let ρ : N → ((G3 A).left ⟶ (G3 B).left) := fun k => (P k ⊗ₘ P k ⊗ₘ P k).left
  have hψ : ∀ k a, thφ A (x3 A) a ≫ φ k = ρ k ≫ thφ B (x3 B) a := fun k a => by
    rw [← hφ k]
    letI := hP k
    exact (CubeMap.ofHom (P k)).psum_comm a.down
  have hρ : ∀ {T : Over S} (a b c : T ⟶ A) k, (lift a (lift b c)).left ≫ ρ k =
      (lift (a ≫ P k) (lift (b ≫ P k) (c ≫ P k))).left := fun a b c k => by
    show (lift a (lift b c) ≫ (P k ⊗ₘ P k ⊗ₘ P k)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := φ) (εp := n) M.isLB M'.isLB w hw (ε := thε) hψ
    c'.isGen c.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV c' (T := 𝟙_ (Over S)) s I') := isCub_cubV c' hI'
      have C : IsCub (cubV c (T := 𝟙_ (Over S)) s I) := isCub_cubV c hI
      have p := prod_cub (1 : 𝟙_ (Over S) ⟶ A) 1 1
        (fun q => bwg w q s (fun i => I (q ≫ φ i)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun k _ => ?_).symm)
      have := hP k
      have o : (1 : 𝟙_ (Over S) ⟶ A) ≫ P k = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ k = _ from hρ 1 1 1 k, o]
      exact (congrArg (· ^ n k) (C.face 1 1)).trans (one_zpow _)) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bwg w q z (fun i => J (q ≫ φ i)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun k _ => ?_)))
  rw [hρ]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ _ Q D' r W pr xe T hn a a' b
  obtain ⟨hpr, -, hcp, w, hw, hpsi⟩ := T
  have hG : GlobalFnsSt := GlobalTheory.lawsAndExpansions.1.1.globalFns
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.M.L y J :=
    ⟨fun ψ => (exists_chart Q.M.isLB (ψ y)).choose, fun ψ => (exists_chart Q.M.isLB (ψ y)).choose_spec⟩
  let P : (Fin r × Fin r) × Fin 4 → (D'.P.A ⟶ Q.B) := fun k => ![pr k.1.1 * pr k.1.2, pr k.1.1, pr k.1.2, 1] k.2
  have hPh : ∀ k, IsMonHom (P k) := by
    rintro ⟨⟨i, j⟩, m⟩
    have := hpr i
    have := hpr j
    fin_cases m
    · exact GlobalTheory.Serre.isMonHom_mul _ _
    · exact hpr i
    · exact hpr j
    · exact GlobalTheory.Serre.isMonHom_one
  have hPl : ∀ k, (P k).left = tensφ pr k := by
    rintro ⟨⟨i, j⟩, m⟩
    fin_cases m <;> rfl
  have key := cubV_prod hG D'.P.isAb D'.cub Q.cub P hPh (tensφ pr) hPl (tensε W) w hw (T := TK R) y J J' hJ hJ'
    (cP D' _ a) (cP D' _ a') (cP D' _ b) _ rfl
  have hψ : ∀ u, val (D'.psi u) (𝟙 _) y J' = bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left) * ∏ i, ∏ j, val (Q.tau (xe u i) (xe u j)) (𝟙 _) y J ^ W i j :=
    fun u => hpsi u y J J' hJ hJ'
  have vt : ∀ u v, val (D'.tau u v) (𝟙 _) y J' = val (D'.psi (u + v)) (𝟙 _) y J' * (val (D'.psi u) (𝟙 _) y J')⁻¹ * (val (D'.psi v) (𝟙 _) y J')⁻¹ * (val D'.rigK (𝟙 _) y J')⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ', val_inv]
  have c0 : cP D' (TK R) 0 = 1 := by
    have := cPoint_add D' (TK R) 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have q0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have hP : ∀ u k, cP D' (TK R) u ≫ P k = toUnit (TK R) ≫ Q.c (![xe u k.1.1 + xe u k.1.2, xe u k.1.1, xe u k.1.2, 0] k.2) := by
    intro u k
    have e : ∀ i, cP D' (TK R) u ≫ pr i = toUnit (TK R) ≫ Q.c (xe u i) := fun i => by
      rw [cP, Category.assoc, hcp]
    obtain ⟨⟨i, j⟩, m⟩ := k
    fin_cases m
    · show cP D' (TK R) u ≫ (pr i * pr j) = toUnit (TK R) ≫ Q.c (xe u i + xe u j)
      rw [MonObj.comp_mul, e, e, Q.c_add, MonObj.comp_mul]
    · exact e i
    · exact e j
    · show cP D' (TK R) u ≫ 1 = toUnit (TK R) ≫ Q.c 0
      rw [q0, MonObj.comp_one, MonObj.comp_one]
  rw [GlobalTheory.TauBimultBox.val_lhs D' hJ' a a' b, val_mul hJ']
  have hC : ∀ u u' v, cubV Q.cub y J (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v) = val (Q.tau u v) (𝟙 _) y J * val (Q.tau u' v) (𝟙 _) y J * (val (Q.tau (u + u') v) (𝟙 _) y J)⁻¹ := fun u u' v => by
    rw [← Q.tau_add u u' v y J hJ, mul_comm, inv_mul_cancel_left]
  have hI := interchange (fun u v => val (Q.tau u v) (𝟙 _) y J) (fun u v => Q.tau_symm u v y J hJ) (fun u u' v => by
    have := (isCub_cubV Q.cub hJ).s12 (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v)
    rw [hC, hC, _root_.mul_assoc, _root_.mul_assoc, mul_comm, mul_comm (val (Q.tau u _) (𝟙 _) y J)] at this
    first | exact this | exact this.symm)
  simp only [hP, hC] at key
  have h1 : cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a + a' + b) := by rw [cPoint_add, cPoint_add]
  have h2 : cP D' (TK R) a * cP D' (TK R) a' = cP D' (TK R) (a + a') := (cPoint_add _ _ _ _).symm
  have h3 : cP D' (TK R) a * cP D' (TK R) b = cP D' (TK R) (a + b) := (cPoint_add _ _ _ _).symm
  have h4 : cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a' + b) := (cPoint_add _ _ _ _).symm
  rw [h1, h2, h3, h4, ← c0] at key
  refine alg W xe
    (fun u => bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left))
    (fun u => val (D'.psi u) (𝟙 _) y J') (fun u v => val (D'.tau u v) (𝟙 _) y J') (fun u v => val (Q.tau u v) (𝟙 _) y J)
    (cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b)) (val D'.rigK (𝟙 _) y J') a a' b
    (Q.val_tau_zero 0 y J hJ) hI hψ vt (hn y J' hJ') ?_
  beta_reduce
  exact key

end GlobalTheory.PolTensBimult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormAbelianVarietyTranslateValue
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

section Val

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem sec_sub_id_eq_val (E : SqExt R) {x : Sp E.B ⟶ X} (hx : x ≫ s = spMap (algebraMap R E.B))
    (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (h : spMap ((E.π : E.C →+* E.B).comp (AlgHom.id R E.C : E.C →+* E.C)) ≫ y = x) (f : Z1 (O (dp0 R) s)) :
    ev f (E.secHom hx E.i E.π_i) - ev f (Thick.trivHom (hx := hy) (T := E.thick x hx) (AlgHom.id R E.C) h) =
      E.val y hy f := by
  subst h
  rfl

theorem val_congr (E : SqExt R) {y y' : Sp E.C ⟶ X} (e : y = y') (hy : y ≫ s = spMap (algebraMap R E.C))
    (hy' : y' ≫ s = spMap (algebraMap R E.C)) (f : Z1 (O (dp0 R) s)) : E.val y hy f = E.val y' hy' f := by
  subst e
  rfl

end Val

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem ev_sec_sub_ev_tan_eq_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v)
    (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) :
    ev f P.sec - ev f (P.tan hv) = (SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f :=
  sec_sub_id_eq_val (SqExt.ofModule K P.B P.B) P.w (P.trx v) (P.tr v).w ((P.isTransl_trx v).red hv) f

theorem dualMap_id (B : Type) [CommRing B] : dualMap (RingHom.id B) = RingHom.id (DualNumber B) :=
  RingHom.ext fun c ↦ by ext <;> simp [dualMap]

@[reducible] def Pt.origin (A : Over (Sp K)) [GrpObj A] : GPt A where
  B := K
  x := η[A].left
  w := by
    rw [Category.comp_id, Over.w η[A]]
    exact (Cris.spMap_id K).symm

theorem isTransl_origin (v : epsR K ⟶ A) : IsTransl (algebraMap K K) η[A].left v v.left := by
  refine ⟨1, Over.homMk (spMap (dualMap (algebraMap K K)) ≫ v.left) (by
      rw [Category.assoc, Over.w v]
      change spMap _ ≫ spMap _ = spMap _
      rw [← Cris.spMap_comp, dualMap_comp_algebraMap]), rfl, rfl, ?_⟩
  rw [_root_.one_mul]
  change spMap (dualMap (RingHom.id K)) ≫ v.left = v.left
  rw [dualMap_id, Cris.spMap_id, Category.id_comp]

theorem origin_trx (v : epsR K ⟶ A) : (Pt.origin A).trx v = v.left :=
  ((Pt.origin A).isTransl_trx v).unique (isTransl_origin v)

end GlobalTheory.CechKS

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def tanFn (v : epsR K ⟶ A) (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) : PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ ((SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f).snd

theorem isNat_tanFn (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) : IsNat ⊤ (tanFn v ω.1) := by
  intro P Q φ _
  have := (SqExt.ofModule K P.B P.B).val_map (SqExt.ofModule K Q.B Q.B) (dualAlg φ.ρ) φ.ρ
    (fun c ↦ (fst_dualAlg φ.ρ c).symm) (fun b ↦ by ext <;> simp) (P.trx v) (P.tr v).w (Q.trx v) (Q.tr v).w
    (φ.tr v).pt ω
  simp only [tanFn]
  rw [this, snd_dualAlg]

theorem tanFn_eq (hA : IsAbelianScheme A) (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A) :
    tanFn v ω.1 P = algebraMap K P.B (tanVal v ω) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ ⊤) ⊤ (fun _ ↦ le_rfl)
    (le_iSup_of_le () le_rfl) (tanFn v ω.1) (fun _ ↦ isNat_tanFn v ω)
  obtain ⟨g₀, rfl⟩ := (GlobalTheory.globalFns_holds (Sp K) A hA).2 g
  have key : ∀ Q : GPt A, tanFn v ω.1 Q = algebraMap K Q.B (valR (𝟙 (Sp K)) ⊤ g₀) := by
    intro Q
    rw [hg () Q (fun _ _ ↦ trivial)]
    have e1 : valR Q.x ⊤ (A.hom.appTop.hom g₀) = valR (Q.x ≫ A.hom) ⊤ g₀ := by
      rw [GlobalTheory.Points.valR_comp Q.x A.hom ⊤ g₀]; rfl
    have e2 : Q.x ≫ A.hom = spMap (algebraMap K Q.B) ≫ 𝟙 (Sp K) :=
      (Category.comp_id (Q.x ≫ A.hom)).symm.trans ((Category.assoc _ _ _).trans (Q.w.trans (Category.comp_id _).symm))
    rw [e1, e2, GlobalTheory.Points.valR_spMap_comp _ _ _ (GlobalTheory.Points.le_preimage_top _)]
  have h0 : tanFn v ω.1 (Pt.origin A) = tanVal v ω := by
    simp only [tanFn]
    rw [tanVal_apply]
    exact congrArg TrivSqZeroExt.snd (val_congr (SqExt.dual K) (origin_trx v) _ _ ω.1)
  rw [key, ← h0, key]
  rfl

theorem ev_sec_sub_ev_tan : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (v : epsR K ⟶ A) (hv : IsTangent v) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A),
    ev ω.1 P.sec - ev ω.1 (P.tan hv) = (TrivSqZeroExt.inr (algebraMap K P.B (tanVal v ω)) : DualNumber P.B) := by
  intro K _ A _ hA v hv ω P
  rw [ev_sec_sub_ev_tan_eq_val P hv ω.1]
  ext
  · rw [TrivSqZeroExt.fst_inr]; exact SqExt.π_val (SqExt.ofModule K P.B P.B) _ _ ω
  · exact tanFn_eq hA v ω P

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarOfInt
section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.AlterationOrder

theorem isFinite_spMap_int (k : Type) [CommRing k] (h : Module.Finite ℤ k) :
    IsFinite (spMap (Int.castRingHom k)) := by
  unfold spMap
  rw [IsFinite.SpecMap_iff]
  change (algebraMap ℤ k).Finite
  exact RingHom.finite_algebraMap.2 h

theorem hom_ext_int {X : Scheme.{0}} (f g : X ⟶ Sp ℤ) : f = g :=
  specZIsTerminal.hom_ext f g

theorem isArithVar_int {k : Type} [CommRing k] {Z : Scheme.{0}} {r : Z ⟶ Sp k} {d : ℕ}
    (h : IsArithVar r d) : IsArithVar (r ≫ spMap (Int.castRingHom k)) d := by
  have := isFinite_spMap_int k h.finite
  obtain ⟨hp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB r).1 h.isProjOver
  refine ⟨inferInstance, inferInstance, h.isIntegral, hL.isProjOver _, ?_, h.dim_eq⟩
  rw [hom_ext_int (_ ≫ spMap (Int.castRingHom ℤ)) (r ≫ spMap (Int.castRingHom k))]
  exact h.flat

theorem isArithVar_of_int {k : Type} [CommRing k] (hd : IsDomain k) (hf : Module.Finite ℤ k)
    {Z : Scheme.{0}} {r : Z ⟶ Sp k} {d : ℕ} (h : IsArithVar (r ≫ spMap (Int.castRingHom k)) d) :
    IsArithVar r d := by
  have := isFinite_spMap_int k hf
  obtain ⟨hp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 h.isProjOver
  have : IsProper r := IsProper.of_comp r (spMap (Int.castRingHom k))
  refine ⟨hd, hf, h.isIntegral, hL.isProjOver _, ?_, h.dim_eq⟩
  rw [hom_ext_int (r ≫ spMap (Int.castRingHom k))
    ((r ≫ spMap (Int.castRingHom k)) ≫ spMap (Int.castRingHom ℤ))]
  exact h.flat

theorem regularAlteration_order : RegularAlteration → ∀ (k : Type) [CommRing k] (Z : Scheme.{0}) [IsIntegral Z] (r : Z ⟶ Sp k) (d : ℕ),
    IsArithVar r d → ∃ (B' : Scheme.{0}) (_ : IsIntegral B') (ρ : B' ⟶ Z), IsArithVar (ρ ≫ r) d ∧
      (∀ b : B', IsRegularLocalRing (B'.presheaf.stalk b)) ∧ ρ (genericPoint B') = genericPoint Z ∧
      ρ.residueDegree (genericPoint B') ≠ 0 := by
  intro H k _ Z _ r d h
  obtain ⟨Y, hY, ρ, h1, h2, h3, h4⟩ := H Z _ d (isArithVar_int h)
  refine ⟨Y, hY, ρ, isArithVar_of_int h.isDomain h.finite ?_, h2, h3, h4⟩
  rwa [Category.assoc]

end GlobalTheory.AlterationOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCanForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {A : Over (Sp R)}

theorem fv_form (β : Form (A.hom ≫ 𝟙 _)) {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) : fv β.1 D D' φ x = 0 :=
  β.2 (trivMap φ x) rfl rfl

variable [GrpObj A] {p : ℕ} {G : PDivGroup p R}

def formDat (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) : Dat t ⟨_, hβ⟩ where
  f := β.1
  cl := rfl
  g := fun _ _ _ _ _ ↦ 0
  add := fun _ _ _ _ _ _ φ _ _ ↦ by simp [fv_form]
  h := 0
  res := fun n ↦ by simp [fv_form]

theorem isCan_form : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A),
    ∃ w : G.omega, (∀ n, w.1 n = cotVal β.1 (t.y n)) ∧ IsCan t ⟨_, hβ⟩ (G.rigOfOmega w) := by
  intro R _ A _ p G t β hβ
  refine ⟨⟨(formDat t β hβ).om, fun n ↦ GlobalTheory.T.torsionTowerPresentation_cotangentPullback_res_rigidification R A p G t _ (formDat t β hβ) n⟩, fun n ↦ ?_,
    formDat t β hβ, 0, _, fun n ↦ ?_, fun _ ↦ rfl, rfl⟩
  · change cotVal β.1 (t.y n) - dUnit R (0 : G.A n) = _
    rw [dUnit, map_zero, sub_zero]
  · change (0 : _) = 0 - (fv β.1 _ _ _ _ - fv β.1 _ _ _ _ - fv β.1 _ _ _ _) - cobOne R (G.A n) 0
    simp [fv_form]

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSplitTorusIntoTorusExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension : ∀ (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω))) [GrpObj H], TorusExtension H → ∀ (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H), IsMonHom v → (∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 → GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) → IsClosedImmersion v.left := by
  first | exact @GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension | exact GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension | (intros; apply GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem cDvr_of_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  intro R R' _ _ _ _ _ _ ρ hR hE
  obtain ⟨hdvr, -, hc0⟩ := hR
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hinj, hfin⟩ := hE
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI := hnoeth
  haveI := hic
  have hinj' : Function.Injective (algebraMap R R') := hinj
  haveI : Ring.DimensionLEOne R' := Ring.DimensionLEOne.of_isIntegral R R'
  haveI : IsDedekindDomain R' := { }
  have hnf : ¬ IsField R' := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj' h)
  have hdvr' : IsDiscreteValuationRing R' := ((IsDiscreteValuationRing.TFAE R' hnf).out 0 2).2 (inferInstance : IsDedekindDomain R')
  exact ⟨hdvr', hcomp, charZero_of_injective_algebraMap hinj'⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeformationChartPointSpecMapStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeformationChartPoint_spec_map : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {Ω : Z.Opens} {δ : Γ(Z, Ω) → Γ(Z, Ω)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω δ u θ Wo g x l) (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'), IsChartPt A' m m' Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) (spMap (ρ : B →+* B') ≫ l) := by
  first | exact @GlobalTheory.CechKS.isChartPt_spMap | exact GlobalTheory.CechKS.isChartPt_spMap | (intros; apply GlobalTheory.CechKS.isChartPt_spMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomialStatement
section
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeGen_wedgeForm_of_formallyEtale_mvPolynomial : ∀ {k A₀ A : Type} [CommRing k] [CommRing A₀] [CommRing A] (α : k →+* A₀) (β : k →+* A)
    (ρ : A₀ →+* A), ρ.comp α = β → ∀ {n r : ℕ} (z : Fin n → A₀) (b : Module.Basis (Fin n) A₀ (Omega α)),
    (∀ i, b i = dFun α (z i)) → ∀ (t : Fin r → A), (MvPolynomial.eval₂Hom ρ t).FormallyEtale →
    IsFreeGen A (dForm β (Fin.append t (fun i => ρ (z i)))) := by
  first | exact @GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | (intros; apply GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenericFibreFractionFieldMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem isGrpPullback_genMap : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (h : IsGrpPullback G' G (spMap ρ) β), IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G) (spMap (fracMap ρ hρ)) (genMap hρ β h.1.w) := by
  intro R R' _ _ _ _ ρ hρ G' _ G _ β h
  have n : IsGrpPullback ((Over.pullback (jK R')).obj G') G (spMap (fracMap ρ hρ) ≫ jK R)
      (genMap hρ β h.1.w ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_pullback G' (jK R')).comp h).congr (jK_comp_spMap ρ hρ) (genMap_fst hρ β h.1.w).symm
  exact IsGrpPullback.cancel (isGrpPullback_pullback G (jK R)) n (genMap_snd hρ β h.1.w)

end GlobalTheory.Mum.GenDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralPullbackRationalSaturationModelOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.UPoinc GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_pullback_rationalSaturation_model_open : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap R.val.toRingHom) → IsIntegral (pullback u₀ (spMap (toRat R))) ∧ ∃ pt : Sp Ω ⟶ pullback u₀ (spMap (toRat R)), pt ≫ pullback.fst _ _ ≫ U₀.ι = M.pt ∧ Dense (Set.range pt) := by
  first | exact @GlobalTheory.UPoinc.isIntegral_pullback_toRat | exact GlobalTheory.UPoinc.isIntegral_pullback_toRat | (intros; apply GlobalTheory.UPoinc.isIntegral_pullback_toRat <;> assumption)
end

