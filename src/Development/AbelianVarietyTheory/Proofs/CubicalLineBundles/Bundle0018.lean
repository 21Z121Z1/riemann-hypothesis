import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorLB

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G A T : Over S} [GrpObj G] [GrpObj A]

theorem lam_sum {I : Type} (s : Finset I) (c : I → Pic A.left) (x y : T ⟶ A) :
    lam (∑ i ∈ s, c i) x y = ∑ i ∈ s, lam (c i) x y := by
  simp only [lam, map_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

variable [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

theorem lam_lam (u v : A ⟶ G) [IsMonHom u] [IsMonHom v] (x y : T ⟶ A) :
    lam (lam (cls L hL) u v) x y =
      lam (cls L hL) (x ≫ u) (y ≫ v) + lam (cls L hL) (y ≫ u) (x ≫ v) := by
  rw [lam.eq_1 (lam (cls L hL) u v)]
  simp only [pull_lam, MonObj.mul_comp, MonObj.one_comp, lam_one_left, lam_mul_left hL hΘ,
    lam_mul_right hL hΘ]
  abel

end Pairing

theorem herm_expand {O : Type} [CommRing O] (bar : O →+* O) {M : Type} [AddCommGroup M] [Module O M]
    (h : M → M → O) (hadd : ∀ m m' n, h (m + m') n = h m n + h m' n)
    (hsmul : ∀ (c : O) m n, h (c • m) n = c * h m n) (hsym : ∀ m n, h n m = bar (h m n))
    (P : Summand O M) (m n : M) :
    h m n = ∑ i, ∑ j, P.incl m i * bar (P.incl n j) *
      h (P.proj (Pi.single i 1)) (P.proj (Pi.single j 1)) := by
  have hx : ∀ m : M, m = ∑ i, P.incl m i • P.proj (Pi.single i 1) := fun m => by
    have e : P.proj (P.incl m) = m := congr($(P.proj_incl) m)
    simp only [← map_smul, ← map_sum]
    rw [← pi_eq_sum_univ', e]
  have lin : ∀ m n : M, h m n = ∑ i, P.incl m i * h (P.proj (Pi.single i 1)) n := fun m n => by
    let f : M →+ O := AddMonoidHom.mk' (fun m => h m n) fun a b => hadd a b n
    have : f m = f (∑ i, P.incl m i • P.proj (Pi.single i 1)) := congrArg f (hx m)
    rw [map_sum] at this
    exact this.trans (Finset.sum_congr rfl fun i _ => hsmul _ _ _)
  rw [lin]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsym n, lin n, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← hsym, _root_.mul_assoc]

theorem exists_lb_hermitian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (O : Type) [CommRing O] (bar : O →+* O) (M : Type) [AddCommGroup M] [Module O M] (h : M → M → O) [Module.Finite O M] [Module.Projective O M] (A : Over S) [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (w : O), L.IsLB → (∃ tθ : LB.Gen (Theta G L), tθ.IsGen) → (∀ c, LBIso (cubeLB G ![fst G G ≫ a.act c, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a.act (bar c)] L)) → ((∀ c, bar (bar c) = c) ∧ (∀ m m' n, h (m + m') n = h m n + h m' n) ∧ (∀ (c : O) m n, h (c • m) n = c * h m n) ∧ ∀ m n, h n m = bar (h m n)) → w + bar w = 1 → ∃ N : LB A.left, N.IsLB ∧ (∃ tθ : LB.Gen (Theta A N), tθ.IsGen) ∧ (∀ m n, LBIso (cubeLB A ![fst G G ≫ t.tmul m, snd G G ≫ t.tmul n] N) (cubeLB G ![fst G G ≫ a.act (h m n), snd G G] L)) := by
  intro S G _ _ L O _ bar M _ _ h _ _ A _ _ a b t w hL hΘ hadj ⟨hbar, hadd, hsmul, hsym⟩ hw
  let P := Summand.choose O M
  let e : Fin P.n → M := fun i => P.proj (Pi.single i 1)
  let p : Fin P.n → (A ⟶ G) := fun i => t.mapLeft (IsTensor.self a) (LinearMap.proj i ∘ₗ P.incl)
  have hp : ∀ m i, t.tmul m ≫ p i = a.act (P.incl m i) := fun m i => by
    simp [p]
  have pm : ∀ i, IsMonHom (p i) := fun i => IsTensor.isMonHom_mapLeft _ _ _
  have am := a.hom
  have adj : ∀ {T : Over S} (x y : T ⟶ G) (c : O),
      lam (cls L hL) (x ≫ a.act c) y = lam (cls L hL) x (y ≫ a.act (bar c)) := by
    intro T x y c
    have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj c)
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  obtain ⟨N, hN, hc⟩ := cls_surj
    (∑ i, ∑ j, lam (cls L hL) (p i ≫ a.act (h (e i) (e j))) (p j ≫ a.act w))
  have key : ∀ {T : Over S} (x y : T ⟶ A), lam (cls N hN) x y =
      ∑ i, ∑ j, (lam (cls L hL) (x ≫ p i ≫ a.act (h (e i) (e j))) (y ≫ p j ≫ a.act w) +
        lam (cls L hL) (y ≫ p i ≫ a.act (h (e i) (e j))) (x ≫ p j ≫ a.act w)) := by
    intro T x y
    rw [hc, lam_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lam_sum]
    exact Finset.sum_congr rfl fun j _ => lam_lam hL hΘ _ _ x y
  refine ⟨N, hN, ?_, fun m n => ?_⟩
  · refine (cls_eq_zero_iff (N := Theta A N) (LB.isLB_linComb hN _ _)).1 ?_
    refine (cls_cube_three hN (fst _ _) (snd _ _ ≫ fst _ _) (snd A (A ⊗ A) ≫ snd _ _)
      (LB.isLB_linComb hN _ _)).trans ?_
    rw [sub_sub, sub_eq_zero, key, key, key]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [MonObj.mul_comp, MonObj.mul_comp, lam_mul_left hL hΘ, lam_mul_right hL hΘ]
    abel
  · refine (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).1 ?_
    refine (cls_cube_two hN _ _ _).trans (Eq.trans ?_ (cls_cube_two hL _ _ _).symm)
    let φ : O →+ Pic (G ⊗ G).left := AddMonoidHom.mk'
      (fun c => lam (cls L hL) (fst G G ≫ a.act c) (snd G G)) fun c d => by
        simp only [a.add, MonObj.comp_mul, lam_mul_left hL hΘ]
    have hφ : ∀ c d, lam (cls L hL) (fst G G ≫ a.act c) (snd G G ≫ a.act d) = φ (c * bar d) := by
      intro c d
      have := adj (fst G G ≫ a.act c) (snd G G) (bar d)
      rw [hbar, Category.assoc, ← a.mul] at this
      exact this.symm
    have hq : ∀ m i c, t.tmul m ≫ p i ≫ a.act c = a.act (P.incl m i * c) := fun m i c => by
      rw [← Category.assoc, hp, a.mul]
    rw [key]
    simp only [Category.assoc, hq, lam_comm _ (snd G G ≫ _), hφ, ← map_add, ← map_sum]
    change _ = φ (h m n)
    congr 1
    have E := herm_expand bar h hadd hsmul hsym P m n
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => P.incl m j * w * bar (P.incl n i * h (e i) (e j))),
      ← _root_.mul_one (h m n), ← hw, mul_add, add_comm, E]
    simp only [Finset.sum_mul, map_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← hsym]; ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

end GlobalTheory.HermTensorLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem hom_deriv_baseChange : ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (R₀ : Type) [CommRing R₀] (ρ : R →+* R₀) (P₀ Q₀ : Out.PolAV (Sp R₀)) (φ : P₀.A.left ⟶ P.A.left) (ψ : Q₀.A.left ⟶ Q.A.left) (v₀ : epsR R₀ ⟶ P₀.A) (t₀ : epsR R₀ ⟶ Q₀.A) (f : P₀.A ⟶ Q₀.A) (a : R₀), IsPolFibre ρ P P₀ φ → IsPolFibre ρ Q Q₀ ψ → IsVecOver ρ φ v v₀ → IsVecOver ρ ψ t t₀ → IsMonHom f → IsLieComb ![a] ![t₀] (v₀ ≫ f) → ∀ (R₁ : Type) [CommRing R₁] (g : R₀ →+* R₁), (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre (g.comp ρ) P P₁ φ₁ → IsPolFibre (g.comp ρ) Q Q₁ ψ₁ → IsVecOver (g.comp ρ) φ₁ v v₁ → IsVecOver (g.comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![g a] ![t₁] (v₁ ≫ f₁)) := by
  intro R _ P Q v t R₀ _ ρ P₀ Q₀ φ ψ v₀ t₀ f a hP hQ hv ht hf hlie R₁ _ g P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP₁ hQ₁ hv₁ ht₁

  obtain ⟨φ', hφ', hφφ⟩ := PolFibre.cancel hP hP₁
  obtain ⟨ψ', hψ', hψψ⟩ := PolFibre.cancel hQ hQ₁
  have hv' : IsVecOver g φ' v₀ v₁ :=
    (PolFibre.vec_iff hP.2.1.1 hφ'.2.1.1.w hv).mpr (by rw [hφφ]; exact hv₁)
  have ht' : IsVecOver g ψ' t₀ t₁ :=
    (PolFibre.vec_iff hQ.2.1.1 hψ'.2.1.1.w ht).mpr (by rw [hψψ]; exact ht₁)

  have hsq : (φ' ≫ f.left) ≫ Q₀.A.hom = P₁.A.hom ≫ spMap g := by
    rw [Category.assoc, Over.w f]
    exact hφ'.2.1.1.w
  let f₁ : P₁.A ⟶ Q₁.A :=
    Over.homMk (hψ'.2.1.1.lift (φ' ≫ f.left) P₁.A.hom hsq) (hψ'.2.1.1.lift_snd _ _ _)
  have hf₁ : f₁.left ≫ ψ' = φ' ≫ f.left := hψ'.2.1.1.lift_fst _ _ _
  have : IsMonHom f := hf
  refine ⟨f₁, GlobalTheory.UU.isMonHom_of_over_isMonHom hφ'.2.1 hψ'.2.1 f f₁ hf₁, ?_⟩

  have hw : (v₁ ≫ f₁).left ≫ ψ' = spMap (Chart.dualMapR g) ≫ (v₀ ≫ f).left := by
    have e : v₁.left ≫ φ' = spMap (Chart.dualMapR g) ≫ v₀.left := hv'
    simp only [Over.comp_left, Category.assoc, hf₁]
    rw [← Category.assoc, e, Category.assoc]
  have key := (lieComb_baseChange R₀ R₁ g Q₀.A Q₁.A ψ' hψ'.2.1 1 ![t₀] (v₀ ≫ f) ![a] ![t₁] (v₁ ≫ f₁)
    (by intro j; fin_cases j; exact ht') hlie).mp hw
  convert key using 1
  funext i
  fin_cases i
  rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivDescendsToNumberField
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace HomDerivDescent

variable {R R' : Type} [CommRing R] [CommRing R']

theorem isLieComb_one_iff {G : Over (Sp R)} [GrpObj G] (a : R) (t w : epsR R ⟶ G) :
    IsLieComb ![a] ![t] w ↔ w.left = spMap (epsScaleR a) ≫ t.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    refine ⟨![w], fun i => ?_, by simp⟩
    fin_cases i
    exact h

theorem epsScaleR_comp_dualMapR (g : R →+* R') (a : R) :
    (epsScaleR (g a)).comp (Chart.dualMapR g) = (Chart.dualMapR g).comp (epsScaleR a) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR, epsScaleR, mul_comm]

theorem isLieComb_pull {g : R →+* R'} {G H : Over (Sp R)} {G' H' : Over (Sp R')} [GrpObj H] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hψ : IsPullback ψ H'.hom H.hom (spMap g))
    {v : epsR R ⟶ G} {t : epsR R ⟶ H} {v' : epsR R' ⟶ G'} {t' : epsR R' ⟶ H'}
    (hv : IsVecOver g φ v v') (ht : IsVecOver g ψ t t') {f : G ⟶ H} {f' : G' ⟶ H'}
    (hf : f'.left ≫ ψ = φ ≫ f.left) {a : R} (h : IsLieComb ![a] ![t] (v ≫ f)) :
    IsLieComb ![g a] ![t'] (v' ≫ f') := by
  rw [isLieComb_one_iff] at h ⊢
  unfold IsVecOver at hv ht
  refine hψ.hom_ext ?_ ?_
  · rw [Over.comp_left] at h ⊢
    rw [Category.assoc, hf, ← Category.assoc, hv, Category.assoc, h, Category.assoc, ht, ← Category.assoc,
      ← Category.assoc]
    congr 1
    exact (spMap_comp_spMap _ _).trans
      ((congrArg spMap (epsScaleR_comp_dualMapR g a).symm).trans (spMap_comp_spMap _ _).symm)
  · rw [Over.w, Category.assoc, Over.w]
    refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
    change spMap _ = _
    congr 1
    ext x <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_descent (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (k : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] (P Q : Out.PolAV (Sp k)) {Pc Qc : Out.PolAV (Sp ℂ)} {φc : Pc.A.left ⟶ P.A.left}
    {ψc : Qc.A.left ⟶ Q.A.left} (hP : IsPolFibre (algebraMap k ℂ) P Pc φc) (hQ : IsPolFibre (algebraMap k ℂ) Q Qc ψc)
    (fc : Pc.A ⟶ Qc.A) [IsMonHom fc] :
    ∃ (K : IntermediateField k ℂ) (P₁ Q₁ : Out.PolAV (Sp K)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left)
      (m : Pc.A.left ⟶ P₁.A.left) (n : Qc.A.left ⟶ Q₁.A.left) (f₁ : P₁.A ⟶ Q₁.A), FiniteDimensional k K ∧
      IsPolFibre (algebraMap k K) P P₁ φ₁ ∧ IsPolFibre (algebraMap k K) Q Q₁ ψ₁ ∧
      IsPolFibre (algebraMap K ℂ) P₁ Pc m ∧ IsPolFibre (algebraMap K ℂ) Q₁ Qc n ∧ m ≫ φ₁ = φc ∧ n ≫ ψ₁ = ψc ∧
      IsMonHom f₁ ∧ fc.left ≫ n = m ≫ f₁.left := by
  obtain ⟨e, he, he'⟩ := grpPullback_iso hP.2.1 (isGrpPullback_pullback P.A _)
  obtain ⟨d, hd, hd'⟩ := grpPullback_iso hQ.2.1 (isGrpPullback_pullback Q.A _)
  obtain ⟨K, f, j, hK, hf, j₁, j₂, j₃⟩ := hom_descends_to_numberField hT hB k P Q (e.inv ≫ fc ≫ d.hom) inferInstance
  obtain ⟨P₁, φ₁, hP₁⟩ := exists_isPolFibre hB (algebraMap k K) P
  obtain ⟨Q₁, ψ₁, hQ₁⟩ := exists_isPolFibre hB (algebraMap k K) Q
  obtain ⟨m, hm, hm'⟩ := PolFibre.cancel (g := algebraMap K ℂ) hP₁ hP
  obtain ⟨n, hn, hn'⟩ := PolFibre.cancel (g := algebraMap K ℂ) hQ₁ hQ
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hP₁.2.1 (isGrpPullback_pullback P.A _)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback Q.A _) hQ₁.2.1
  refine ⟨K, P₁, Q₁, φ₁, ψ₁, m, n, a.hom ≫ f ≫ b.hom, hK, hP₁, hQ₁, hm, hn, hm', hn', inferInstance, ?_⟩
  have key : m ≫ a.hom.left = e.hom.left ≫ j := by
    apply pullback.hom_ext
    · exact ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) ha').trans hm')).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₁).trans he')).symm
    · exact ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (Over.w a.hom)).trans hm.2.1.1.w)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₂).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (Over.w e.hom))))).symm
  refine hQ₁.2.1.1.hom_ext ?_ ?_
  · have r : e.hom.left ≫ (e.inv ≫ fc ≫ d.hom).left = fc.left ≫ d.hom.left := by
      rw [← Over.comp_left, e.hom_inv_id_assoc, Over.comp_left]
    rw [Category.assoc, hn', Over.comp_left, Over.comp_left]
    simp only [Category.assoc]
    rw [hb', ← Category.assoc, key, Category.assoc, ← hd', ← Category.assoc, ← r, Category.assoc]
    exact congrArg (e.hom.left ≫ ·) j₃.symm
  · rw [Category.assoc, Category.assoc, Over.w, hn.2.1.1.w, hm.2.1.1.w, ← Category.assoc, Over.w]

end HomDerivDescent

open HomDerivDescent in

theorem hom_deriv_descends_to_numberField : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (k : IntermediateField ℚ ℂ) (ρ : R →+* k) (α : ℂ), FiniteDimensional ℚ k → IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp ℂ)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR ℂ ⟶ P₁.A) (t₁ : epsR ℂ ⟶ Q₁.A), IsPolFibre ((algebraMap k ℂ).comp ρ) P P₁ φ₁ → IsPolFibre ((algebraMap k ℂ).comp ρ) Q Q₁ ψ₁ → IsVecOver ((algebraMap k ℂ).comp ρ) φ₁ v v₁ → IsVecOver ((algebraMap k ℂ).comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![α] ![t₁] (v₁ ≫ f₁)) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (a : K₁), FiniteDimensional ℚ K₁ ∧ (a : ℂ) = α ∧ (∀ (P₁ Q₁ : Out.PolAV (Sp K₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR K₁ ⟶ P₁.A) (t₁ : epsR K₁ ⟶ Q₁.A), IsPolFibre ((IntermediateField.inclusion hk).toRingHom.comp ρ) P P₁ φ₁ → IsPolFibre ((IntermediateField.inclusion hk).toRingHom.comp ρ) Q Q₁ ψ₁ → IsVecOver ((IntermediateField.inclusion hk).toRingHom.comp ρ) φ₁ v v₁ → IsVecOver ((IntermediateField.inclusion hk).toRingHom.comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) := by
  intro hT hB R _ P Q v t k ρ α hk hv hbas hhom
  obtain ⟨Pk, φk, hPk⟩ := exists_isPolFibre hB ρ P
  obtain ⟨Qk, ψk, hQk⟩ := exists_isPolFibre hB ρ Q
  obtain ⟨Pc, φc, hPc⟩ := exists_isPolFibre hB (algebraMap k ℂ) Pk
  obtain ⟨Qc, ψc, hQc⟩ := exists_isPolFibre hB (algebraMap k ℂ) Qk
  have hPc' := PolFibre.comp hPk hPc
  have hQc' := PolFibre.comp hQk hQc
  obtain ⟨vc, hvc, -⟩ := existsUnique_isVecOver hPc'.2.1.1 v
  obtain ⟨tc, htc, -⟩ := existsUnique_isVecOver hQc'.2.1.1 t
  obtain ⟨fc, hfc, hα⟩ := hhom Pc Qc _ _ vc tc hPc' hQc' hvc htc
  obtain ⟨K, P₀, Q₀, φ₀, ψ₀, m, n, f₀, hK, hP₀, hQ₀, hm, hn, em, en, hf₀, ef⟩ :=
    exists_descent hT hB k Pk Qk hPc hQc fc
  have hP₀' := PolFibre.comp hPk hP₀
  have hQ₀' := PolFibre.comp hQk hQ₀
  obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hP₀'.2.1.1 v
  obtain ⟨t₀, ht₀, -⟩ := existsUnique_isVecOver hQ₀'.2.1.1 t
  obtain ⟨c, hc, -⟩ := (hbas _ _ _ _ _ hQ₀' ht₀).2 (v₀ ≫ f₀)
    (HomDescent.isTangent_comp f₀ (hv₀.isTangent hP₀'.2.1 hv))
  obtain ⟨a, rfl⟩ : ∃ a, c = ![a] := ⟨c 0, by ext i; fin_cases i; rfl⟩
  have hv' : IsVecOver (algebraMap K ℂ) m v₀ vc :=
    (PolFibre.vec_iff hP₀'.2.1.1 hm.2.1.1.w hv₀).2 (by rw [← Category.assoc, em]; exact hvc)
  have ht' : IsVecOver (algebraMap K ℂ) n t₀ tc :=
    (PolFibre.vec_iff hQ₀'.2.1.1 hn.2.1.1.w ht₀).2 (by rw [← Category.assoc, en]; exact htc)
  have hα' := isLieComb_pull hn.2.1.1 hv' ht' ef hc
  have haα : algebraMap K ℂ a = α := congrFun (((hbas _ _ _ _ _ hQc' htc).2 (vc ≫ fc)
    (HomDescent.isTangent_comp fc (hvc.isTangent hPc'.2.1 hv))).unique hα' hα) 0
  have main : ∀ (P₁ Q₁ : Out.PolAV (Sp K)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left)
      (v₁ : epsR K ⟶ P₁.A) (t₁ : epsR K ⟶ Q₁.A), IsPolFibre ((algebraMap k K).comp ρ) P P₁ φ₁ →
      IsPolFibre ((algebraMap k K).comp ρ) Q Q₁ ψ₁ → IsVecOver ((algebraMap k K).comp ρ) φ₁ v v₁ →
      IsVecOver ((algebraMap k K).comp ρ) ψ₁ t t₁ →
      ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁) := by
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP₁ hQ₁ hv₁ ht₁
    obtain ⟨p, hp, rfl⟩ := PolFibre.cancel (g := RingHom.id K) hP₀' hP₁
    obtain ⟨q, hq, rfl⟩ := PolFibre.cancel (g := RingHom.id K) hQ₀' hQ₁
    obtain ⟨f₁, hf₁, e₁⟩ := HomDescent.exists_isMonHom_pull hp.2.1 hq.2.1 f₀
    exact ⟨f₁, hf₁, isLieComb_pull hq.2.1.1 ((PolFibre.vec_iff hP₀'.2.1.1 hp.2.1.1.w hv₀).2 hv₁)
      ((PolFibre.vec_iff hQ₀'.2.1.1 hq.2.1.1.w ht₀).2 ht₁) e₁ hc⟩
  have : IsScalarTower ℚ k K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hfin : FiniteDimensional ℚ K := Module.Finite.trans k K
  exact ⟨K.restrictScalars ℚ, fun x hx => K.algebraMap_mem ⟨x, hx⟩, a, hfin, haα, main⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivativeClosure
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.HomDerivative

theorem isLieComb_inv {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {v x : epsR R ⟶ G} {a : R}
    (hv : IsTangent v) (hx : IsLieComb ![a] ![v] x) : IsLieComb ![-a] ![v] x⁻¹ := by
  obtain ⟨y, hy⟩ : ∃ y, IsLieComb ![-a] ![v] y :=
    ⟨_, (GlobalTheory.LieMultiple.isLieComb_one_iff_comp (-a) v _).2 rfl⟩
  have hsum := (GlobalTheory.LieMultiple.lieMultiple_calculus R G G v x y a (-a)).2.1 hv hx hy
  have hone := (GlobalTheory.LieMultiple.lieMultiple_calculus R G G v x y a (-a)).2.2.2.2.2 hv
  rw [add_neg_cancel] at hsum
  have hxy : x * y = 1 :=
    ((GlobalTheory.LieMultiple.isLieComb_one_iff_comp 0 v _).1 hsum).trans
      ((GlobalTheory.LieMultiple.isLieComb_one_iff_comp 0 v _).1 hone).symm
  rw [← eq_inv_of_mul_eq_one_right hxy]
  exact hy

theorem hom_derivative_closure : Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (S : Set R₁), IsTangent t → (∀ a ∈ S, (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre ρ P P₁ φ₁ → IsPolFibre ρ Q Q₁ ψ₁ → IsVecOver ρ φ₁ v v₁ → IsVecOver ρ ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁))) → ∀ a ∈ AddSubgroup.closure S, (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre ρ P P₁ φ₁ → IsPolFibre ρ Q Q₁ ψ₁ → IsVecOver ρ φ₁ v v₁ → IsVecOver ρ ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) := by
  intro _ R _ P Q v t R₁ _ ρ S ht hS a ha
  induction ha using AddSubgroup.closure_induction with
  | mem a h => exact hS a h
  | zero =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    refine ⟨toUnit _ ≫ η, inferInstance, ?_⟩
    have h1 : v₁ ≫ toUnit P₁.A ≫ η[Q₁.A] = 1 := by
      rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (v₁ ≫ toUnit _) (toUnit _)]
      rfl
    rw [h1]
    exact (GlobalTheory.LieMultiple.lieMultiple_calculus R₁ Q₁.A Q₁.A t₁ t₁ t₁ 0 0).2.2.2.2.2 hT
  | add a b _ _ iha ihb =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    obtain ⟨f, hf, hfa⟩ := iha P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    obtain ⟨g, hg, hgb⟩ := ihb P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    refine ⟨lift f g ≫ μ, inferInstance, ?_⟩
    change IsLieComb _ _ (v₁ ≫ (f * g))
    rw [MonObj.comp_mul]
    exact (GlobalTheory.LieMultiple.lieMultiple_calculus R₁ Q₁.A Q₁.A t₁ (v₁ ≫ f) (v₁ ≫ g) a b).2.1 hT hfa hgb
  | neg a _ iha =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    obtain ⟨f, hf, hfa⟩ := iha P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    refine ⟨f⁻¹, inferInstance, ?_⟩
    rw [GrpObj.comp_inv]
    exact isLieComb_inv hT hfa

end GlobalTheory.HomDerivative
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralDerivativeCurveHomGoodReduction
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace HomIntegral

theorem isLieComb_single_iff {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨fun _ => w, fun i => by fin_cases i; exact h, by simp⟩

theorem isLieComb_fibre {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} {G H : Over (Sp R)} [GrpObj H]
    {G' H' : Over (Sp R')} [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hψ : IsPullback ψ H'.hom H.hom (spMap g)) {F : G ⟶ H} {f : G' ⟶ H'} (hf : f.left ≫ ψ = φ ≫ F.left)
    {v : epsR R ⟶ G} {t : epsR R ⟶ H} {v' : epsR R' ⟶ G'} {t' : epsR R' ⟶ H'} (hv : IsVecOver g φ v v')
    (ht : IsVecOver g ψ t t') {b : R} (h : IsLieComb ![b] ![t] (v ≫ F)) : IsLieComb ![g b] ![t'] (v' ≫ f) := by
  rw [isLieComb_single_iff] at h ⊢
  unfold IsVecOver at hv ht
  refine hψ.hom_ext ?_ ?_
  · rw [Over.comp_left] at h
    rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, hv, Category.assoc, h, Category.assoc, ht,
      ← Category.assoc, ← Category.assoc]
    congr 1
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    congr 1
    ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [Over.w, Category.assoc, Over.w t']
    refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
    change spMap _ = spMap _
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_extension {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] [GrpObj H]
    (h : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f →
      ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback j).map F = f)
    {G' H' : Over S'} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃ F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hψ (isGrpPullback_pullback H j)
  obtain ⟨F, ⟨hF, e⟩, -⟩ := h (a.inv ≫ f ≫ b.hom) inferInstance
  refine ⟨F, hF, ?_⟩
  have e₁ : ((Over.pullback j).map F).left ≫ pullback.fst H.hom j = pullback.fst G.hom j ≫ F.left :=
    pullback.lift_fst _ _ _
  have e₂ : f ≫ b.hom = a.hom ≫ (Over.pullback j).map F := by rw [e, Iso.hom_inv_id_assoc]
  rw [← ha', ← hb', ← Category.assoc, ← Over.comp_left, e₂, Over.comp_left, Category.assoc, Category.assoc]
  exact congrArg (a.hom.left ≫ ·) e₁

end HomIntegral

open HomIntegral in

theorem isIntegral_of_hom_derivative : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.PolBaseChangeSt → ∀ (M : Type) [Field M] [NumberField M] (P Q : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (t : epsR (𝓞 M) ⟶ Q.A) (a : M), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) Q Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) → IsIntegral ℤ a := by
  intro hext hB M _ _ P Q v t a hv ht hf
  have key : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 M),
      a ∈ Localization.subalgebra.ofField M _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors := by
    intro 𝔭
    set T := Localization.subalgebra.ofField M _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors with hT
    have : IsDiscreteValuationRing T :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 M) 𝔭.ne_bot T
    have : IsFractionRing T M := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.asIdeal.primeCompl T M
    have e : (algebraMap T M).comp (algebraMap (𝓞 M) T) = algebraMap (𝓞 M) M :=
      (IsScalarTower.algebraMap_eq _ _ _).symm
    obtain ⟨P₀, φ₀, hP₀⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) T) P
    obtain ⟨Q₀, ψ₀, hQ₀⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) T) Q
    obtain ⟨P₁, φ₁, hP₁⟩ := exists_isPolFibre hB (algebraMap T M) P₀
    obtain ⟨Q₁, ψ₁, hQ₁⟩ := exists_isPolFibre hB (algebraMap T M) Q₀
    obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hP₀.2.1.1 v
    obtain ⟨t₀, ht₀, -⟩ := existsUnique_isVecOver hQ₀.2.1.1 t
    obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver hP₁.2.1.1 v₀
    obtain ⟨t₁, ht₁, -⟩ := existsUnique_isVecOver hQ₁.2.1.1 t₀
    have hP := e ▸ PolFibre.comp hP₀ hP₁
    have hQ := e ▸ PolFibre.comp hQ₀ hQ₁
    have hv' := e ▸ (PolFibre.vec_iff hP₀.2.1.1 hP₁.2.1.1.w hv₀).1 hv₁
    have ht' := e ▸ (PolFibre.vec_iff hQ₀.2.1.1 hQ₁.2.1.1.w ht₀).1 ht₁
    obtain ⟨f, hfm, hfa⟩ := hf P₁ Q₁ _ _ v₁ t₁ hP hQ hv' ht'
    obtain ⟨F, hF, hFf⟩ := exists_extension (hext T M P₀.A Q₀.A (isSemiAbelian_of_isAbelianScheme _ P₀.isAb)
      (isSemiAbelian_of_isAbelianScheme _ Q₀.isAb)) hP₁.2.1 hQ₁.2.1 f
    have tv₀ := hv₀.isTangent hP₀.2.1 hv
    obtain ⟨c, hc, -⟩ := (ht T _ Q₀ ψ₀ t₀ hQ₀ ht₀).2 _ (isTangent_comp_of_isMonHom F v₀ tv₀)
    have ec : c = ![c 0] := by funext i; fin_cases i; rfl
    rw [ec] at hc
    have h₁ := isLieComb_fibre hQ₁.2.1.1 hFf hv₁ ht₁ hc
    have u := ((ht M _ Q₁ _ t₁ hQ ht').2 _
      (isTangent_comp_of_isMonHom f v₁ (hv₁.isTangent hP₁.2.1 tv₀))).unique hfa h₁
    have ea : a = algebraMap T M (c 0) := congrFun u 0
    rw [ea]
    exact (c 0).2
  have h := Algebra.mem_iInf.2 key
  rw [IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at h
  obtain ⟨x, rfl⟩ := h
  exact x.isIntegral_coe

end GlobalTheory
end
end

