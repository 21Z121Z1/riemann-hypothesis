import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0177
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisE8FactorTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis

theorem omegaStd_eq_sum (g : ℕ) (a b : Fin g ⊕ Fin g → ℤ) :
    omegaStd a b = ∑ c, ∑ d, Out.stdSymp g (((finCongr (two_mul g)).trans finSumFinEquiv.symm).symm c)
      (((finCongr (two_mul g)).trans finSumFinEquiv.symm).symm d) * (a c * b d) := by
  set σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm with hσ
  have l : ∀ a, (σ.symm (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (σ.symm (.inr a) : ℕ) = g + a := fun _ => rfl
  have ll : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r]; split_ifs <;> omega
  have rr : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r]; split_ifs <;> omega
  have lr : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega
  have rl : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega
  simp only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]
  simp [sub_eq_add_neg]

theorem exists_family {N g : ℕ} (hN : Odd N) {T R : Type} [CommGroup T] [CommRing R] [IsDomain R] {z : Rˣ}
    (hz : IsPrimitiveRoot z N) (hT : ∀ x : T, x ^ N = 1)
    (hc : ∀ d : ℕ, d ∣ N → Nat.card {x : T // x ^ d = 1} = d ^ (2 * g))
    (E : Matrix (Fin 8) (Fin 8) ℤ) (hE : E.transpose = E) (hdet : E.det = 1)
    (e : (Fin 8 → T) →* (Fin 8 → T) →* Rˣ) (halt : ∀ x, e x x = 1) (hnd : ∀ x, (∀ y, e x y = 1) → x = 1)
    (hrel : ∀ s t s' t' : Fin 8 → ℤ, dotProduct s (E.mulVec t) = dotProduct s' (E.mulVec t') → ∀ p q : T,
      e (fun u => p ^ s u) (fun u => q ^ t u) = e (fun u => p ^ s' u) (fun u => q ^ t' u)) :
    ∃ b : Fin g ⊕ Fin g → T, ∀ x y : Fin 8 → (Fin g ⊕ Fin g → ℤ),
      e (fun u => ∏ c, b c ^ x u c) (fun u => ∏ c, b c ^ y u c) = z ^ ∑ u, ∑ v, E u v * omegaStd (x u) (y v) := by
  let s₀ : Fin 8 → ℤ := Pi.single 0 1
  let t₀ : Fin 8 → ℤ := E.adjugate.mulVec s₀
  have h₀ : dotProduct s₀ (E.mulVec t₀) = 1 := by
    simp only [t₀, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec]
    simp [s₀]
  have h₀' : dotProduct t₀ (E.mulVec s₀) = 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hE, dotProduct_comm, h₀]
  let pw : (Fin 8 → ℤ) → T →* (Fin 8 → T) := fun s =>
    MonoidHom.mk' (fun p u => p ^ s u) fun p q => funext fun u => mul_zpow p q _
  let h : T →* T →* Rˣ := ((e.comp (pw s₀)).flip.comp (pw t₀)).flip
  have hh : ∀ p q, h p q = e (fun u => p ^ s₀ u) (fun u => q ^ t₀ u) := fun _ _ => rfl
  have key : ∀ (s t : Fin 8 → ℤ) (p q : T),
      e (fun u => p ^ s u) (fun u => q ^ t u) = h p q ^ dotProduct s (E.mulVec t) := fun s t p q => by
    rw [hrel s t (dotProduct s (E.mulVec t) • s₀) t₀ (by rw [smul_dotProduct, h₀, smul_eq_mul, _root_.mul_one]), hh,
      ← MonoidHom.zpow_apply, ← map_zpow]
    congr 2
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, Pi.pow_apply]
    rw [← zpow_mul, _root_.mul_comm]
  have eskew : ∀ x y, e x y * e y x = 1 := fun x y => by
    have := halt (x * y)
    simp only [map_mul, MonoidHom.mul_apply, halt, _root_.one_mul, _root_.mul_one] at this
    first | exact this | (rw [_root_.mul_comm]; exact this)
  have halt' : ∀ p, h p p = 1 := fun p => by
    have k₁ : h p p ^ 2 = 1 := by
      have := eskew (fun u => p ^ s₀ u) (fun u => p ^ t₀ u)
      rwa [key, key, h₀, h₀', zpow_one, ← pow_two] at this
    have k₂ : h p p ^ N = 1 := by rw [← map_pow, hT, map_one]
    obtain ⟨m, rfl⟩ := hN
    rwa [pow_succ, pow_mul, k₁, one_pow, _root_.one_mul] at k₂
  have hnd' : ∀ p, (∀ q, h p q = 1) → p = 1 := fun p hp => by
    have := hnd (fun u => p ^ s₀ u) fun y => by
      have hy : y = ∏ v, fun u => y v ^ (Pi.single v 1 : Fin 8 → ℤ) u := by
        funext u
        rw [Finset.prod_apply, Finset.prod_eq_single u (fun v _ hv => by simp [Pi.single_apply, hv.symm]) (by simp)]
        simp
      rw [hy, map_prod]
      exact Finset.prod_eq_one fun v _ => by rw [key, hp, one_zpow]
    simpa [s₀] using congrFun this 0
  obtain ⟨v, hv⟩ := exists_stdSymp_of_alternating_pairing N g T R z hN.pos hz hT hc h halt' hnd'
  let σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm
  refine ⟨fun c => v (σ.symm c), fun x y => ?_⟩
  have hp : ∀ x : Fin 8 → (Fin g ⊕ Fin g → ℤ),
      (fun u => ∏ c, v (σ.symm c) ^ x u c) = ∏ c, fun u => v (σ.symm c) ^ x u c := fun x =>
    funext fun u => by rw [Finset.prod_apply]
  rw [hp, hp]
  simp only [map_prod, MonoidHom.finset_prod_apply, key, hv, ← zpow_mul]
  have zs : ∀ {α : Type} [Fintype α] (f : α → ℤ), ∏ a, z ^ f a = z ^ ∑ a, f a := fun f =>
    (map_prod (zpowersHom Rˣ z) (fun a => Multiplicative.ofAdd (f a)) Finset.univ).symm
  simp only [zs]
  congr 1
  simp only [omegaStd_eq_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun u _ => ?_))
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun u' _ => ?_))
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [σ]
  ring

theorem exists_basis : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ N : ℕ), Odd N → ∀ (K : Type) [Field K] [IsAlgClosed K], (N : K) ≠ 0 →
  ∀ (z : Kˣ), IsPrimitiveRoot z N → ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (P'.A ⟶ B)), E8Fibration.IsProd pr →
  (∀ (s t s' t' : Fin 8 → ℤ), dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
    ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
    ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
      (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
      ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c) →
  ∃ b : Fin gQ ⊕ Fin gQ → (Out.baseOver (Sp K) ⟶ B), (∀ c, b c ^ N = 1) ∧
    ∀ (x y : Fin 8 → (Fin gQ ⊕ Fin gQ → ℤ)) (X Y : Out.baseOver (Sp K) ⟶ P'.A),
      (∀ u, X ≫ pr u = ∏ c, b c ^ x u c) → (∀ u, Y ≫ pr u = ∏ c, b c ^ y u c) →
      Out.WeilIs P'.A P'.L N X Y (unitOn z ^ ∑ u, ∑ v, E8Fibration.e8 W u v * omegaStd (x u) (y v)) := by
  intro W hW g N hN K _ _ hK z hz P hg B _ _ pr hpr hrel
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have : IsDomain Γ(Sp K, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have hz' : IsPrimitiveRoot (unitOn z) N :=
    hz.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)
      (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1)
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P N (Out.baseOver _)
  have hmon := hpr.1
  let φ₀ : (Out.baseOver (Sp K) ⟶ P.A) →* (Fin 8 → (Out.baseOver (Sp K) ⟶ B)) :=
    MonoidHom.mk' (fun x u => x ≫ pr u) fun x y => funext fun u => MonObj.mul_comp _ _ _
  have hφ : Function.Bijective φ₀ :=
    ⟨fun x y h => (hpr.2 _ (φ₀ y)).unique (fun u => congrFun h u) fun _ => rfl,
      fun y => (hpr.2 _ y).exists.imp fun x hx => funext hx⟩
  let φ := MulEquiv.ofBijective φ₀ hφ
  have φa : ∀ x u, φ x u = x ≫ pr u := fun _ _ => rfl
  let T : Subgroup (Out.baseOver (Sp K) ⟶ B) := (powMonoidHom N).ker
  let ψ : (Fin 8 → T) →* (Out.baseOver (Sp K) ⟶ P.A) :=
    φ.symm.toMonoidHom.comp (T.subtype.compLeft (Fin 8))
  have ψa : ∀ x u, ψ x ≫ pr u = (x u).1 := fun x u =>
    (φa _ u).symm.trans (congrFun (φ.apply_symm_apply _) u)
  have hT : ∀ x : T, x ^ N = 1 := fun x => Subtype.ext x.2
  have ψt : ∀ x, ψ x ^ N = 1 := fun x => by
    rw [← map_pow, show x ^ N = 1 from funext fun u => hT _, map_one]
  have ψs : ∀ y : Out.baseOver (Sp K) ⟶ P.A, y ^ N = 1 → ∃ x, ψ x = y := fun y hy =>
    ⟨fun u => ⟨φ y u, by
      show φ y u ^ N = 1
      rw [← Pi.pow_apply, ← map_pow, hy, map_one, Pi.one_apply]⟩, φ.symm_apply_apply y⟩
  choose w hw hw' using fun x y : Fin 8 → T => w₁ _ _ (ψt x) (ψt y)
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (by rw [map_mul]; exact w₂ _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (CommPairing.weilIs_symm P.isLB (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : (Fin 8 → T) →* (Fin 8 → T) →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  have hc : ∀ d : ℕ, d ∣ N → Nat.card {x : T // x ^ d = 1} = d ^ (2 * g) := fun d hd => by
    have hA : Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} = d ^ (2 * P.g) :=
      (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd hN.pos)).2.2.2.2 K (𝟙 _) (by
        obtain ⟨e, rfl⟩ := hd
        rw [Nat.cast_mul] at hK
        exact left_ne_zero_of_mul hK)
    let F : (Fin 8 → {x : T // x ^ d = 1}) → {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} := fun x =>
      ⟨ψ fun u => (x u).1, by
        rw [← map_pow, show (fun u => (x u).1) ^ d = 1 from funext fun u => (x u).2, map_one]⟩
    have hF : Function.Bijective F := by
      refine ⟨fun x y h => funext fun u => Subtype.ext (Subtype.ext ?_), fun y => ?_⟩
      · have h' : ψ (fun u => (x u).1) = ψ fun u => (y u).1 := congrArg Subtype.val h
        rw [← ψa (fun u => (x u).1) u, h', ψa]
      · obtain ⟨x, hx⟩ := ψs y.1 (by
          obtain ⟨c, hc⟩ := hd
          rw [hc, pow_mul, y.2, one_pow])
        refine ⟨fun u => ⟨x u, Subtype.ext ?_⟩, Subtype.ext hx⟩
        show (x u).1 ^ d = 1
        rw [← ψa, hx, ← φa, ← Pi.pow_apply, ← map_pow, y.2, map_one, Pi.one_apply]
    have h := Nat.card_eq_of_bijective F hF
    rw [hA, hg, Nat.card_fun, Nat.card_fin, show 2 * (8 * g) = 2 * g * 8 by ring, pow_mul] at h
    exact Nat.pow_left_injective (by norm_num) h
  obtain ⟨b, hb⟩ := exists_family (g := g) hN hz' hT hc (E8Fibration.e8 W)
    (by simp [e8, Matrix.transpose_add, add_comm]) hW.2 e
    (fun x => (hw' _ _ _ (w₃ _ (ψt x))).symm)
    (fun x hx => by
      have h1 : ψ x = 1 := hL.weilNondeg K P N hK _ (ψt x) fun y hy => by
        obtain ⟨y, rfl⟩ := ψs y hy
        have h : w x y = 1 := hx y
        exact h ▸ hw x y
      funext u
      exact Subtype.ext (by rw [← ψa, h1, ← φa, map_one]; rfl))
    (fun s t s' t' h p q => hw' _ _ _ (hrel s t s' t' h p.1 q.1 p.2 q.2 _ _ _ _
      (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) _ (hw _ _)))
  refine ⟨fun c => (b c).1, fun c => (b c).2, fun x y X Y hX hY => ?_⟩
  have hp : ∀ (x : Fin 8 → (Fin g ⊕ Fin g → ℤ)) (X : Out.baseOver (Sp K) ⟶ P.A),
      (∀ u, X ≫ pr u = ∏ c, (b c).1 ^ x u c) → X = ψ fun u => ∏ c, b c ^ x u c := fun x X hX =>
    hφ.1 (funext fun u => (hX u).trans (Eq.symm ((ψa _ u).trans (by simp))))
  rw [hp x X hX, hp y Y hY, ← hb x y]
  exact hw _ _

end GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelRootsFiniteExtCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FieldLevel

open GlobalTheory.TorsionGenerators

theorem pairing_prod {H U : Type} [CommGroup H] [CommGroup U] (e : H →* H →* U) (z : U) {g : ℕ}
    (x : Fin g ⊕ Fin g → H) (h₁ : ∀ i j, e (x (.inl i)) (x (.inl j)) = 1)
    (h₂ : ∀ i j, e (x (.inr i)) (x (.inr j)) = 1)
    (h₃ : ∀ i j, e (x (.inl i)) (x (.inr j)) = if i = j then z else 1)
    (h₄ : ∀ i j, e (x (.inr i)) (x (.inl j)) = if i = j then z⁻¹ else 1) (a b : Fin g ⊕ Fin g → ℤ) :
    e (∏ i, x i ^ a i) (∏ i, x i ^ b i) = z ^ omegaStd a b := by
  have hz : z ^ omegaStd a b = ∏ i, z ^ (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)) :=
    (map_prod (zpowersHom U z) (fun i => Multiplicative.ofAdd
      (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))) Finset.univ)
  have hi : ∀ (p : Prop) [Decidable p] (u : U) (m : ℤ), (if p then u else 1) ^ m = if p then u ^ m else 1 :=
    fun p _ u m => by split_ifs <;> simp
  rw [hz]
  simp only [map_prod, map_zpow, MonoidHom.finset_prod_apply, MonoidHom.zpow_apply, Fintype.prod_sum_type,
    map_mul, MonoidHom.mul_apply, h₁, h₂, h₃, h₄, one_zpow, Finset.prod_const_one, _root_.one_mul, _root_.mul_one,
    hi, Finset.prod_ite_eq, Finset.prod_ite_eq', Finset.mem_univ, if_true, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [← zpow_mul, inv_zpow', ← zpow_add, zpow_sub, ← zpow_neg]
  congr 1
  ring

theorem stdSymp_mk {g p q : ℕ} (hp : p < 2 * g) (hq : q < 2 * g) : stdSymp g ⟨p, hp⟩ ⟨q, hq⟩ =
    if p < g ∧ q = p + g then 1 else if q < g ∧ p = q + g then -1 else 0 := rfl

theorem exists_points (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) [IsCommMonObj P.A] {g : ℕ}
    (hg : g = P.g) (M : ℕ) (hM : (M : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (hz : IsPrimitiveRoot ze M) :
    ∃ x : Fin g ⊕ Fin g → (baseOver (Sp K) ⟶ P.A), (∀ i, x i ^ M = 1) ∧
      ∀ a b : Fin g ⊕ Fin g → ℤ, Out.WeilIs P.A P.L M (∏ i, x i ^ a i) (∏ i, x i ^ b i) (ze ^ omegaStd a b) := by
  obtain ⟨x, hx, hw⟩ := ConstThetaLevel.exists_symplectic_points hL K P hg M hM ze hz
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P M (baseOver (Sp K))
  let H : Subgroup (baseOver (Sp K) ⟶ P.A) := (powMonoidHom M).ker
  have hH : ∀ x : H, x.1 ^ M = 1 := fun x => x.2
  choose c hc hu using fun x y : H => w₁ x.1 y.1 (hH x) (hH y)
  have l : ∀ x x' y, c (x * x') y = c x y * c x' y := fun x x' y => (hu _ _ _ (w₂ _ _ _ _ _ (hc x y) (hc x' y))).symm
  have s : ∀ x y, c y x = (c x y)⁻¹ := fun x y => (hu _ _ _ (CommPairing.weilIs_symm P.isLB (hc x y))).symm
  let e : H →* H →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (c x) fun y y' => by
    rw [s (y * y'), l, mul_inv, ← s, ← s]) fun x x' => MonoidHom.ext fun y => l x x' y
  let κ : Fin g ⊕ Fin g → Fin (2 * g) := Sum.elim (fun i => ⟨i, by omega⟩) (fun i => ⟨i + g, by omega⟩)
  let y : Fin g ⊕ Fin g → H := fun i => ⟨x (κ i), hx _⟩
  have he : ∀ i j, e (y i) (y j) = ze ^ stdSymp g (κ i) (κ j) := fun i j => (hu (y i) (y j) _ (hw _ _)).symm
  refine ⟨fun i => (y i).1, fun i => hH _, fun a b => ?_⟩
  have E := pairing_prod e ze y (fun i j => ?_) (fun i j => ?_) (fun i j => ?_) (fun i j => ?_) a b
  · have h := hc (∏ i, y i ^ a i) (∏ i, y i ^ b i)
    rw [show c (∏ i, y i ^ a i) (∏ i, y i ^ b i) = _ from E] at h
    simpa only [SubmonoidClass.coe_finset_prod, SubgroupClass.coe_zpow] using h
  all_goals
    have hi := i.2
    have hj := j.2
    rw [he]
    simp only [κ, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff]
    rw [stdSymp_mk]
    split_ifs <;> first | omega | (simp; done)

theorem exists_level_and_roots : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (K : Type) [Field K] [CharZero K] (j : R →+* K) (n : ℕ), 0 < n → ∀ (ζ : Kˣ), IsPrimitiveRoot ζ n → ∀ (r : ℕ) (c : Fin r → (𝟙_ (Over (Sp R)) ⟶ P.A)), ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (lev : (Fin P.g ⊕ Fin P.g → ℤ) → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)) (d : Fin r → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)), (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ n = 1) ∧ (∀ x y, Out.WeilIs P.A P.L n (lev x) (lev y) (unitOn (Units.map (algebraMap K L).toMonoidHom ζ ^ omegaStd x y))) ∧ ∀ i, d i ^ n = toUnit _ ≫ c i := by
  intro R _ P K _ _ j n hn ζ hζ r c
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have := P.isAb.smooth
  let Q := AlgebraicClosure K
  let t : R →+* Q := (algebraMap K Q).comp j
  have hnQ : (n : Q) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hz : IsPrimitiveRoot (Units.map (algebraMap K Q).toMonoidHom ζ) n :=
    hζ.map_of_injective (unitsMap_injective _)
  obtain ⟨P', φ', β, h, -, H⟩ := exists_fibre hL P t
  have := P'.isAb.comm
  obtain ⟨x, hx, hw⟩ := exists_points hL Q P' h.1.symm n hnQ _ (ZH.RealDimOne.isPrimitiveRoot_unitOn hz)
  have hroot : ∀ p : Over.mk (spMap t) ⟶ P.A, ∃ q, q ^ n = p := fun p => by
    obtain ⟨p, rfl⟩ := β.surjective p
    obtain ⟨q, hq⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_div hL.mulN P' p n hn
    exact ⟨β q, (map_pow β _ _).symm.trans (congrArg β hq)⟩
  choose d hd using fun i => hroot (toUnit _ ≫ c i)
  let z : (Fin P.g ⊕ Fin P.g) ⊕ Fin r → (Over.mk (spMap t) ⟶ P.A) := Sum.elim (fun i => β (x i)) d
  choose s hs hb using fun i => exists_finite_coordinates P.A.hom t (z i).left (Over.w _)
  let s' : Set Q := ⋃ i, s i
  have : Finite s' := (Set.finite_iUnion hs).to_subtype
  let L := IntermediateField.adjoin K s'
  have : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin fun y _ =>
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let io : L →+* Q := algebraMap L Q
  let j' : R →+* L := (algebraMap K L).comp j
  have hj : io.comp j' = t := rfl
  choose b hb' using fun i => hb i L io io.injective (fun c => ⟨j' c, rfl⟩) (fun y hy =>
    ⟨⟨y, IntermediateField.subset_adjoin K s' (Set.mem_iUnion.2 ⟨i, hy⟩)⟩, rfl⟩)
  have hbw : ∀ i, b i ≫ P.A.hom = spMap j' := fun i => by
    have := TorsionSeparable.epi_specMap io
    rw [← cancel_epi (spMap io), ← Category.assoc, hb', spMap_comp_spMap]
    exact Over.w (z i)
  let y : _ → (Over.mk (spMap j') ⟶ P.A) := fun i => Over.homMk (b i) (hbw i)
  have hy : ∀ i, extPt hj ≫ y i = z i := fun i => Over.OverMorphism.ext (hb' i)
  let F : (Over.mk (spMap j') ⟶ P.A) →* (Over.mk (spMap t) ⟶ P.A) :=
    MonoidHom.mk' (fun p => extPt hj ≫ p) fun p q => comp_mul _ _ _
  have hF : ∀ a : Fin P.g ⊕ Fin P.g → ℤ, extPt hj ≫ (∏ i, y (.inl i) ^ a i) = β (∏ i, x i ^ a i) := fun a => by
    show F _ = _
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, map_zpow]
    exact congrArg (· ^ a i) (hy (.inl i))
  have hyM : ∀ i, y (.inl i) ^ n = 1 := fun i => by
    rw [← extPt_eq_one_iff hj, comp_pow, hy]
    exact (map_pow β _ _).symm.trans ((congrArg β (hx i)).trans (map_one β))
  have hT : ∀ a : Fin P.g ⊕ Fin P.g → ℤ, (∏ i, y (.inl i) ^ a i) ^ n = 1 := fun a => by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm, zpow_mul, zpow_natCast, hyM, one_zpow]
  refine ⟨L, inferInstance, inferInstance, this, fun a => ∏ i, y (.inl i) ^ a i, fun i => y (.inr i),
    fun a a' => ?_, hT, fun a a' => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · obtain ⟨u, hu⟩ := exists_weilIs hL P j' (hT a) (hT a')
    have H₁ := weilIs_extPt hL P hj hu
    rw [hF, hF] at H₁
    have e := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H₁ (H _ _ _ _ (hw a a'))
    have hζ' : Units.map (algebraMap K Q).toMonoidHom ζ =
      Units.map io.toMonoidHom (Units.map (algebraMap K L).toMonoidHom ζ) := Units.ext rfl
    rw [← ZH.RealDimOne.unitOn_zpow, hζ', ← map_zpow] at e
    rwa [← unitsMap_injective io (unitOn_injective e)]
  · apply extPt_injective hj
    rw [comp_pow, hy, ← Category.assoc, comp_toUnit]
    exact hd i

end GlobalTheory.FieldLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorBundleRigidification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensRig

theorem oneGen_isGen' {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem eta_eq_one {S : Scheme.{0}} (B : Over S) [GrpObj B] : (η[B] : 𝟙_ (Over S) ⟶ B) = 1 := by
  show _ = toUnit _ ≫ η[B]
  rw [toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]

theorem eSec_tensφ {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {r : ℕ} (pr : Fin r → (A ⟶ B))
    (hpr : ∀ i, IsMonHom (pr i)) (k : (Fin r × Fin r) × Fin 4) : eSec A ≫ tensφ pr k = eSec B := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  have hi : η[A] ≫ pr i = η[B] := IsMonHom.one_hom _
  have hj : η[A] ≫ pr j = η[B] := IsMonHom.one_hom _
  have key : ∀ x : A ⟶ B, η[A] ≫ x = η[B] → eSec A ≫ x.left = eSec B := fun x hx => by
    rw [eSec, eSec, ← Over.comp_left, hx]
  fin_cases m
  · refine key _ ?_
    rw [MonObj.comp_mul, hi, hj, eta_eq_one, _root_.mul_one]
  · exact key _ hi
  · exact key _ hj
  · refine key _ ?_
    rw [MonObj.comp_one, eta_eq_one]

end GlobalTheory.Mum.TensRig

open GlobalTheory.Mum.TensRig in
theorem GlobalTheory.Mum.TensRig.rig_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)), (∀ i, IsMonHom (pr i)) → ∀ (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∃ rig : LB.Gen (L'.pull (eSec A')), rig.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val (LB.pullGen L' _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' * gm (ptK η[A']) z _ (w.s (fun k => J (ptK η[A'] ≫ tensφ pr k), J' (ptK η[A']))) = 1 := by
  intro R _ _ D r W A' _ L' hL' pr hpr w hw
  have hform : FormEq (X := D.P.A.left) (Y := (𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (PEmpty.elim : PEmpty → _) PEmpty.elim
      (GlobalTheory.LamBiext.flatφ (tensφ pr) (fun _ : PUnit => eSec A'))
      (GlobalTheory.LamBiext.flatε (tensε W) (fun _ : PUnit => (1 : ℤ))) := by
    intro U _ h
    simp only [GlobalTheory.LamBiext.flatφ, GlobalTheory.LamBiext.flatε, eSec_tensφ pr hpr, one_mul, Finset.univ_eq_empty,
      Finset.prod_empty, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε]
    simp
  obtain ⟨t, ht, htv⟩ := exists_gen D.P.isLB hform (LB.oneGen D.P.L) (oneGen_isGen' _)
  obtain ⟨a, ha, hmaps⟩ := Transport.exists_transport
    (DVR.linComb_isLB L' hL' (fun _ : PUnit => eSec A') (fun _ => 1))
    (DVR.linComb_isLB _ (DVR.linComb_isLB D.P.L D.P.isLB (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A') (fun _ => 1))
    (LB.linCombIso w (fun _ : PUnit => eSec A') (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _)
    (GlobalTheory.LamBiext.nest D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t)
    (GlobalTheory.LamBiext.nest_isGen ht)
  refine ⟨a, ha, fun z J J' hJ hJ' => ?_⟩
  have hPM := (GlobalTheory.GtCubeCompare.maps_iff_pm w (fun _ : PUnit => eSec A') (fun _ => 1) a _).1 hmaps
  have hp : (toUnit (TK R)).left z ∈ LB.wchart (LB.LinComb D.P.L (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (ptK η[A'] ≫ tensφ pr k)
  have hq : (toUnit (TK R)).left z ∈ LB.wchart L' (fun _ : PUnit => eSec A') (fun _ => J' (ptK η[A'])) :=
    Set.mem_iInter.2 fun _ => hJ' (ptK η[A'])
  have E := hPM _ (toUnit (TK R)).left z _ _ hp hq
  have L1 : gm (toUnit (TK R)).left z (LB.wchart (LB.LinComb D.P.L (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)))
      ((GlobalTheory.LamBiext.nest D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t).s
        (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k))) = 1 := by
    refine (gm_res _ z (GlobalTheory.LamBiext.nest_le D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') _) hp _).trans ?_
    exact (val_of t (toUnit (TK R)).left z J (fun p => J (ptK η[A'] ≫ tensφ pr p.2))
      (fun x => congrArg J (Category.assoc _ _ _).symm)).symm.trans ((htv _ _ z J hJ).trans (val_one _))
  rw [L1, Fintype.prod_unique, zpow_one] at E
  rw [val_pull hJ' a (toUnit (TK R)).left (𝟙 _),
    val_of a _ z J' (fun _ => J' (ptK η[A'])) (fun _ => by rw [Category.id_comp]; rfl), Category.id_comp, mul_comm]
  exact E.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemRealisationRegularAtPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (𝔭 : Ideal R), 𝔭.IsPrime → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), (∀ x ∈ S.R, ∃ a b : R, b ∉ 𝔭 ∧ x = (a : Ω) / (b : Ω)) ∧ S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₁ ^ (S.r * S.N)).left ∧ (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₂ ^ (S.r * S.N)).left := by
  first | exact @GlobalTheory.ThetaRealAt.exists_thetaSys_real_at | exact GlobalTheory.ThetaRealAt.exists_thetaSys_real_at | (intros; apply GlobalTheory.ThetaRealAt.exists_thetaSys_real_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSystem_spread_of_level_fractionField : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [CharZero R₁] (A₁ : PolAV (Sp (FractionRing R₁))), (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) → ∀ (n k j : ℕ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : R₁) → ∀ (ζ : R₁ˣ), ReciprocityTheory.ChartRestriction.G.Out.Level A₁ ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ)) → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : GlobalTheory.ZH.ArithBase o Ω) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (b : o →+* R₁) (e : Ω →+* FractionRing R₁) (φ : A₁.A.left ⟶ ρS.P.A.left), S.g = A₁.g ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) ∧ IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ ∧ LBIso A₁.L (ρS.P.L.pull φ) := by
  first | exact @GlobalTheory.Mum.exists_thetaSys_spread | exact GlobalTheory.Mum.exists_thetaSys_spread | (intros; apply GlobalTheory.Mum.exists_thetaSys_spread <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitExtensionDivisibleValuationForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitInputExt

theorem exists_ext_dvd_rational : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (O : Type) [CommRing O] (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∀ N : ℕ, 0 < N → ∃ (T : Formalism.L2.Pj.CDVR) (ρ : R →+* T.V) (b : O →+* T.V) (ϖ : T.V) (D' : DegData T.V (maximalIdeal T.V)), Function.Injective ρ ∧ ρ.Finite ∧ Function.Injective b ∧ Irreducible ϖ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ (∀ Q : D'.toPre.X → ℤ, ReciprocityTheory.ChartRestriction.G.DVR.QForm.IsQ D'.toPre ϖ Q → ∀ u v, (N : ℤ) ∣ ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf D'.toPre Q u v) ∧ ∀ k : ℕ, k ∣ N → ∀ q : QkPt D'.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D'.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q := by
  intro R _ _ _ D O _ V₁ _ _ _ ρ₁ b₁ hV₁ iρ₁ fρ₁ lρ₁ ib₁ N hN
  obtain ⟨D₁, ⟨h₁⟩⟩ := GlobalTheory.MumPull.exists_pull R V₁ ρ₁ iρ₁ lρ₁ D
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff V₁).1 hV₁
  let T₁ : Formalism.L2.Pj.CDVR := { V := V₁ }
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V₁
  obtain ⟨T', g, ϖ, e, ig, fg, hϖ, he, hass, rat⟩ :=
    GlobalTheory.QkRationalExt.exists_cdvr_ext_rational T₁ D₁.toPre D₁.tau_bimult N hN π hπ
  have lg : IsLocalHom g := fg.to_isIntegral.isLocalHom ig
  obtain ⟨D', ⟨hD⟩⟩ := GlobalTheory.MumPull.exists_pull V₁ T'.V g ig lg D₁
  have hc : Nonempty (IsPullDeg (g.comp ρ₁) D.toPre D'.toPre) :=
    GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R V₁ T'.V ρ₁ g D.toPre D₁.toPre D'.toPre ig ⟨h₁⟩ ⟨hD⟩
  choose Q₁ hQ₁ using ReciprocityTheory.ChartRestriction.G.DVR.QForm.exists_QVal hπ D₁
  have hNe : (N : ℤ) ∣ (e : ℤ) := by exact_mod_cast he
  refine ⟨T', g.comp ρ₁, g.comp b₁, ϖ, D', ig.comp iρ₁, fg.comp fρ₁, ig.comp ib₁, hϖ, hc, ?_, ?_⟩
  · intro Q hQ u v
    have hq : ∀ y, Q y = e * Q₁ (hD.xe y) := fun y =>
      ReciprocityTheory.ChartRestriction.G.DVR.QForm.QVal_unique hϖ D' (hQ y)
        (GlobalTheory.QValPull.main T₁ T' g D₁.toPre D'.toPre hD π ϖ e ig hπ hϖ hass y _ (hQ₁ _))
    rw [ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf, hq, hq, hq]
    exact dvd_sub (dvd_sub (hNe.mul_right _) (hNe.mul_right _)) (hNe.mul_right _)
  · intro k hk
    exact rat D'.toPre hD D'.tau_bimult k hk

end GlobalTheory.TraitInputExt
end
end

