import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0044
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicPeriodicCocycleCoboundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocDerRegularCoeff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubWeilPerfectOfGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PerfectPairing
variable {O : Type} [CommRing O]

theorem exists_rep [IsLocalRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    (hfin : IsFinite ((𝟙 A) ^ n : A ⟶ A).left) (hflat : Flat ((𝟙 A) ^ n : A ⟶ A).left) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra O H), Module.Free O H ∧ Module.Finite O H ∧
      ∃ y : specO O H ⟶ A, y ^ n = 1 ∧ ∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ A), z ^ n = 1 →
        ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z := by
  obtain ⟨H, φ, y, hφf, hφl, hpb⟩ := finRep_exists_isPullback_spec ((𝟙 A) ^ n : A ⟶ A).left
    (CommRingCat.of O) (eSec A)
  letI : Algebra O H := φ.hom.toAlgebra
  haveI : Module.Finite O H := hφf
  haveI : Module.Flat O H := hφl
  have hpow : ∀ {T : Over (Sp O)} (z : T ⟶ A),
      z.left ≫ ((𝟙 A) ^ n : A ⟶ A).left = (z ^ n).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have he : eSec A ≫ A.hom = 𝟙 _ := Over.w (η[A])
  have hy : y ≫ A.hom = (specO O H).hom := by
    rw [← Over.w ((𝟙 A) ^ n : A ⟶ A), ← Category.assoc, hpb.w, Category.assoc, he]
    exact Category.comp_id _
  let y' : specO O H ⟶ A := Over.homMk y hy
  refine ⟨H, inferInstance, inferInstance, Module.free_of_flat_of_isLocalRing, inferInstance, y', ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [← hpow, GlobalTheory.UU.one_left]
    exact hpb.w
  · intro S _ _ z hz
    have hw : z.left ≫ ((𝟙 A) ^ n : A ⟶ A).left =
        Spec.map (CommRingCat.ofHom (algebraMap O S)) ≫ eSec A := by
      rw [hpow, hz, GlobalTheory.UU.one_left]
      rfl
    let l : Spec (CommRingCat.of S) ⟶ Spec H := hpb.lift _ _ hw
    have hl : Spec.map (Spec.preimage l) = l := Spec.map_preimage l
    have h1 : φ ≫ Spec.preimage l = CommRingCat.ofHom (algebraMap O S) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hl]
      exact hpb.lift_snd _ _ hw
    refine ⟨⟨(Spec.preimage l).hom, fun r => congrArg (fun f => f.hom r) h1⟩, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change Spec.map (Spec.preimage l) ≫ y = z.left
      rw [hl]
      exact hpb.lift_fst _ _ hw
    · intro ψ hψ
      have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom : H ⟶ CommRingCat.of S) = l := by
        apply hpb.hom_ext
        · rw [hpb.lift_fst _ _ hw, ← hψ]
          rfl
        · rw [hpb.lift_snd _ _ hw, ← Spec.map_comp]
          congr 1
          ext r
          exact ψ.commutes r
      have h3 := Spec.map_injective (h2.trans hl.symm)
      ext a
      exact congrArg (fun f => f.hom a) h3

theorem isReduced_rep {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {H : Type} [CommRing H] [Algebra O H]
    [Module.Finite O H] {y : specO O H ⟶ A} (hy : y ^ n = 1)
    (hu : ∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ A), z ^ n = 1 →
      ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra O F] (hn : (n : F) ≠ 0) : _root_.IsReduced (F ⊗[O] H) := by
  refine TorsionReduced.isReduced_of_forall_dualNumber F _ fun φ b => ?_
  let χ : H →ₐ[O] DualNumber F := (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
  have hz : (ptMap χ ≫ y) ^ n = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have h2 := TorsionReduced.eq_const_of_pow_eq_one hn.isUnit _ hz
  simp only [← Category.assoc] at h2
  rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap] at h2
  have h4 := (hu _ _ hz).unique rfl h2.symm
  have h5 : ∀ a, (χ a).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (congrArg (fun f => f a) h4)
    simpa using this
  induction b with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f a =>
    have : f ⊗ₜ[O] a = f • ((1 : F) ⊗ₜ[O] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_smul, TrivSqZeroExt.snd_smul]
    exact smul_eq_zero_of_right f (h5 a)

theorem eq_one_of_affine {A : Over (Sp O)} [GrpObj A] {T : Over (Sp O)} (x : T ⟶ A)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (ρ : specO O S ⟶ T), ρ ≫ x = 1) : x = 1 := by
  apply Over.OverMorphism.ext
  refine T.left.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (T.left.affineOpenCover.f i ≫ T.hom)
  letI : Algebra O (T.left.affineOpenCover.X i) := ψ.hom.toAlgebra
  let ρ : specO O (T.left.affineOpenCover.X i) ⟶ T := Over.homMk (T.left.affineOpenCover.f i) hψ.symm
  have := (h _ ρ).trans (MonObj.comp_one ρ).symm
  exact congrArg (fun q => q.left) this

section Val
variable {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (n : ℕ)
  {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']

def Val (x y : specO O S ⟶ A) (s : S) : Prop :=
  ∃ ζ, GlobalTheory.UU.CubWeil c n x y ζ ∧ (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ζ.val = s

variable {c n} {x x' y y' : specO O S ⟶ A} {s s' : S}

theorem Val.exists (hx : x ^ n = 1) (hy : y ^ n = 1) : ∃ s, Val c n x y s := by
  obtain ⟨ζ, h, -⟩ := GlobalTheory.UU.existsUnique_cubWeil c hx hy
  exact ⟨_, ζ, h, rfl⟩

theorem Val.unique (h : Val c n x y s) (h' : Val c n x y s') : s = s' := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  rw [h.unique h']

theorem Val.isUnit (h : Val c n x y s) : IsUnit s := by
  obtain ⟨ζ, h, rfl⟩ := h
  exact ζ.isUnit.map _

theorem val_one_iff : Val c n x y 1 ↔ GlobalTheory.UU.CubWeil c n x y 1 := by
  refine ⟨fun ⟨ζ, h, e⟩ => ?_, fun h => ⟨1, h, map_one _⟩⟩
  have : ζ = 1 := Units.ext ((ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom).1 (e.trans (map_one _).symm))
  exact this ▸ h

theorem Val.mul_left (h : Val c n x y s) (h' : Val c n x' y s') : Val c n (x * x') y (s * s') := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  exact ⟨_, h.mul_left h', map_mul _ _ _⟩

theorem Val.mul_right (h : Val c n x y s) (h' : Val c n x y' s') : Val c n x (y * y') (s * s') := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  have := (h.symm.mul_left h'.symm).symm
  rw [mul_inv, inv_inv, inv_inv] at this
  exact ⟨_, this, map_mul _ _ _⟩

theorem Val.comp (h : Val c n x y s) (f : S →ₐ[O] S') : Val c n (ptMap f ≫ x) (ptMap f ≫ y) (f s) := by
  obtain ⟨ζ, h, rfl⟩ := h
  refine ⟨_, h.comp (ptMap f), ?_⟩
  exact congrArg (fun q => q.hom ζ.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.toRingHom))

theorem exists_matrix (c : CubicalStr A L) {H : Type} [CommRing H] [Algebra O H] {r : ℕ} (b : Module.Basis (Fin r) O H)
    {y : specO O H ⟶ A} (hy : y ^ n = 1) :
    ∃ D : Matrix (Fin r) (Fin r) O, ∀ (S : Type) [CommRing S] [Algebra O S] (φ ψ : H →ₐ[O] S),
      Val c n (ptMap φ ≫ y) (ptMap ψ ≫ y) (∑ i, ∑ j, algebraMap O S (D i j) * φ (b i) * ψ (b j)) := by
  have hz : ∀ χ : H →ₐ[O] H ⊗[O] H, (ptMap χ ≫ y) ^ n = 1 := fun χ => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  obtain ⟨e, he⟩ := Val.exists (c := c) (hz Algebra.TensorProduct.includeLeft) (hz Algebra.TensorProduct.includeRight)
  refine ⟨fun i j => (b.tensorProduct b).repr e (i, j), fun S _ _ φ ψ => ?_⟩
  have h := he.comp (Algebra.TensorProduct.productMap φ ψ)
  rw [← Category.assoc, ← Category.assoc, TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap,
    Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right] at h
  convert h using 1
  conv_rhs => rw [← (b.tensorProduct b).sum_repr e]
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def,
    _root_.mul_assoc]

end Val

theorem algHom_eq_of_isUnit_det {H S : Type} [CommRing H] [Algebra O H] [CommRing S] [Algebra O S] {r : ℕ}
    (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (hD : IsUnit D.det) (φ φ' : H →ₐ[O] S)
    (h : ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j) =
      ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ' (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j)) : φ = φ' := by
  have key : ∀ ψ : H →ₐ[O] S,
      ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (ψ (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j) =
        ∑ j, (Matrix.vecMul (fun i => ψ (b i)) (D.map (algebraMap O S)) j) • Algebra.TensorProduct.basis S b j := by
    intro ψ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.vecMul, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul', mul_comm]
  rw [key, key] at h
  have h1 := (Algebra.TensorProduct.basis S b).equivFun.symm.injective
    (((Algebra.TensorProduct.basis S b).equivFun_symm_apply _).trans
      (h.trans ((Algebra.TensorProduct.basis S b).equivFun_symm_apply _).symm))
  have hD' : IsUnit (D.map (algebraMap O S)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := hD.map (algebraMap O S)
    rwa [RingHom.map_det] at this
  have h2 := (Matrix.vecMul_injective_of_isUnit hD') h1
  exact AlgHom.toLinearMap_injective (b.ext fun i => congrFun h2 i)

end GlobalTheory.PerfectPairing

namespace GlobalTheory
open PerfectPairing in

theorem cubWeil_perfect_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → ∀ (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ (L : RigLB A) (c : CubicalStr A L) (n : ℕ), 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Nat.card {x : specO O K ⟶ A // x ^ n = 1} = n ^ (2 * g) → (∀ x : specO O K ⟶ A, x ^ n = 1 → (∀ y : specO O K ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → (∀ (T' : Over (Sp O)) (ρ : T' ⟶ T) (y : T' ⟶ A), y ^ n = 1 → GlobalTheory.UU.CubWeil c n (ρ ≫ x) y 1) → x = 1 := by
  intro O K _ _ _ _ _ _ _ hinj A _ _ g hsm L c n hn hfin hflat hcard hK T x hx hT
  obtain ⟨H, _, _, _, _, y, hy, hu⟩ := exists_rep A n hfin hflat
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hred := isReduced_rep hy hu K hnK
  let b := Module.finBasis O H
  obtain ⟨D, hD⟩ := exists_matrix c b hy
  have hz : ∀ {S : Type} [CommRing S] [Algebra O S] (χ : H →ₐ[O] S), (ptMap χ ≫ y) ^ n = 1 := fun χ => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  let Γ : Subgroup (specO O K ⟶ A) := (powMonoidHom n).ker
  choose pt hpt using fun a : Γ => (hu K a.1 a.2).exists
  have hbij : Function.Bijective pt := by
    refine ⟨fun a a' e => Subtype.ext (by rw [← hpt, ← hpt, e]), fun χ => ⟨⟨ptMap χ ≫ y, hz χ⟩, ?_⟩⟩
    exact (hu K _ (hz χ)).unique (hpt _) rfl
  let X : Γ → Γ → K := fun a a' => ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)
  have hX : ∀ a a' : Γ, Val c n a.1 a'.1 (X a a') := fun a a' => by
    have := hD K (pt a) (pt a')
    rwa [hpt, hpt] at this
  have hr : Module.finrank O H = n ^ (2 * g) := by
    rw [← (GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange O H K hred).2.1, ← Nat.card_eq_of_bijective pt hbij]
    exact hcard
  have hdet : IsUnit D.det := by
    refine GlobalTheory.T.isUnit_det_pairing_of_bicharacter_of_dvd_trace O H K Γ _ b D pt X ((n : O) ^ g) hinj hred hbij (fun _ _ => rfl)
      (fun a a' => (hX a a').isUnit.ne_zero) (fun a a' d => (hX _ _).unique ((hX a d).mul_left (hX a' d)))
      (fun a d d' => (hX _ _).unique ((hX a d).mul_right (hX a d'))) (fun a ha => Subtype.ext ?_) (fun h0 => ?_) ?_
      (GlobalTheory.pow_dvd_trace_torsion O A n H y g hsm hy hu)
    · refine hK a.1 a.2 fun z hz => val_one_iff.1 ?_
      have := hX a ⟨z, hz⟩
      rwa [ha] at this
    · have := congrArg (algebraMap O K) h0
      rw [map_pow, map_natCast, map_zero] at this
      exact pow_ne_zero g hnK this
    · rw [hr, Nat.cast_pow, mul_comm, pow_mul]
  refine eq_one_of_affine x fun S _ _ ρ => ?_
  obtain ⟨φ, hφ, -⟩ := hu S (ρ ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  obtain ⟨φ', hφ', -⟩ := hu S 1 (one_pow n)
  let l : S →ₐ[O] S ⊗[O] H := Algebra.TensorProduct.includeLeft
  let m : H →ₐ[O] S ⊗[O] H := Algebra.TensorProduct.includeRight
  have h1 := hD _ (l.comp φ) m
  have h2 := hD _ (l.comp φ') m
  rw [← TangentPow.ptMap_comp_ptMap, Category.assoc] at h1 h2
  rw [hφ, ← Category.assoc] at h1
  rw [hφ', MonObj.comp_one] at h2
  have e1 := h1.unique (val_one_iff.2 (hT _ _ _ (hz m)))
  have e2 := h2.unique (val_one_iff.2 (GlobalTheory.UU.cubWeil_one_left c (hz m)))
  rw [← hφ, ← hφ', algHom_eq_of_isUnit_det b D hdet φ φ' (e1.trans e2.symm)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticKodairaSpencerClass
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Exist

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem const_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

theorem ptDer_add {X : Scheme.{0}} {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f + δ' W f) where
  add W hW f f' := by rw [h.add W hW, h'.add W hW]; ring
  mul W hW f f' := by rw [h.mul W hW, h'.mul W hW]; ring
  res W W' e hW f := by rw [h.res W W' e hW, h'.res W W' e hW]

theorem locDer_sub {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → ℂ}
    {W₀ W₁ : X.Opens} {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D W₀ d)
    (h' : LocDer q p m D W₁ d') : LocDer q p m (fun _ => 0) (W₀ ⊓ W₁) (fun W f => d W f - d' W f) where
  add W hW f f' := by rw [h.add W (hW.trans inf_le_left), h'.add W (hW.trans inf_le_right)]; ring
  mul W hW f f' := by rw [h.mul W (hW.trans inf_le_left), h'.mul W (hW.trans inf_le_right)]; ring
  res W W' e hW f := by rw [h.res W W' e (hW.trans inf_le_left), h'.res W W' e (hW.trans inf_le_right), map_sub]
  base W hW r := by rw [h.base W (hW.trans inf_le_left), h'.base W (hW.trans inf_le_right), sub_self, const_zero]

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
  (m : A₀.left ⟶ X)

theorem ex_hom (z : Fin g → ℂ) : (u.ex z).left ≫ A₀.hom = 𝟙 _ := Over.w (u.ex z)

theorem ex_per (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem dom_open (W : X.Opens) : IsOpen (dom u m W) := (u.hol (m ⁻¹ᵁ W) 0).1

theorem dom_inf {W W' : X.Opens} {z : Fin g → ℂ} : z ∈ dom u m (W ⊓ W') ↔ z ∈ dom u m W ∧ z ∈ dom u m W' :=
  top_le_preimage_inf _ _ _

theorem dom_per (l : u.Λ) (W : X.Opens) (z : Fin g → ℂ) : z + l ∈ dom u m W ↔ z ∈ dom u m W := by
  simp only [dom, Set.mem_setOf_eq, ex_per]

theorem val_hol (W : X.Opens) (c : Γ(A₀.left, m ⁻¹ᵁ W)) :
    DifferentiableOn ℂ (fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) c) (dom u m W) := (u.hol (m ⁻¹ᵁ W) c).2

theorem fn_hol (W : X.Opens) (f : Γ(X, W)) : DifferentiableOn ℂ (fn u m W f) (dom u m W) := by
  have : fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f) :=
    funext fun z => (valAt'_comp _ _ _ _).symm
  rw [this]
  exact val_hol u m W _

theorem fn_diffAt {W : X.Opens} (f : Γ(X, W)) {z : Fin g → ℂ} (hz : z ∈ dom u m W) :
    DifferentiableAt ℂ (fn u m W f) z :=
  (fn_hol u m W f).differentiableAt ((dom_open u m W).mem_nhds hz)

theorem fderiv_res {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {z : Fin g → ℂ}
    (hz : z ∈ dom u m W') : fderiv ℂ (fn u m W' (resG X h f)) z = fderiv ℂ (fn u m W f) z := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [(dom_open u m W').mem_nhds hz] with y hy
  exact valAt'_res _ h f hy

theorem fderiv_per (l : u.Λ) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) :
    fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  simp only [fn, ex_per]

theorem ptDer_fderiv (z w : Fin g → ℂ) :
    PtDer ((u.ex z).left ≫ m) (fun W f => fderiv ℂ (fn u m W f) z w) where
  add W hW f f' := by
    have : fn u m W (f + f') = fn u m W f + fn u m W f' := funext fun y => valAt'_add _ _ _ _
    rw [this, fderiv_add (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]; rfl
  mul W hW f f' := by
    have : fn u m W (f * f') = fn u m W f * fn u m W f' := funext fun y => valAt'_mul _ _ _ _
    rw [this, fderiv_mul (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]; rfl
  res W W' h hW f := by rw [fderiv_res u m h f hW]

theorem fderiv_const_eq {R : Type} [CommRing R] {x₀ : R →+* ℂ} {p : X ⟶ Sp R} (hm : m ≫ p = A₀.hom ≫ spMap x₀)
    (r : R) (z w : Fin g → ℂ) : fderiv ℂ (fn u m ⊤ (constFn p ⊤ r)) z w = 0 := by
  have : fn u m ⊤ (constFn p ⊤ r) =
      fun _ => valAt' (spMap x₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    funext y
    refine (valAt'_appLE _ p ⊤ ⊤ le_top _ le_top).trans ?_
    rw [Category.assoc, hm, ← Category.assoc, ex_hom]
    exact congrArg (fun x => valAt' x ⊤ _) (Category.id_comp _)
  rw [this]
  simp

def ev (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (z : Fin g → ℂ) (W : X.Opens)
    (f : Γ(X, W)) : ℂ :=
  valAt' (u.ex z).left (m ⁻¹ᵁ (W ⊓ W₀)) (d (W ⊓ W₀) (resG X inf_le_left f))

variable {R : Type} [CommRing R] {p : X ⟶ Sp R} {D : R → ℂ} {W₀ : X.Opens}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)}

theorem ev_eq (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} {W W' : X.Opens} (h : W' ≤ W) (h₀ : W' ≤ W₀)
    (hz : z ∈ dom u m W') (f : Γ(X, W)) :
    ev u m W₀ d z W f = valAt' (u.ex z).left (m ⁻¹ᵁ W') (d W' (resG X h f)) := by
  rw [ev, ← res_res (inf_le_left : W ⊓ W₀ ≤ W) (le_inf h h₀), hd.res _ _ _ inf_le_right]
  exact (valAt'_res (u.ex z).left (V := m ⁻¹ᵁ W') _ _ hz).symm

theorem ptDer_ev (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} (hz : z ∈ dom u m W₀) :
    PtDer ((u.ex z).left ≫ m) (ev u m W₀ d z) where
  add W hW f f' := by
    simp only [ev, map_add, hd.add _ inf_le_right, valAt'_add]
  mul W hW f f' := by
    have h : z ∈ dom u m (W ⊓ W₀) := (dom_inf u m).2 ⟨hW, hz⟩
    simp only [ev, map_mul, hd.mul _ inf_le_right, valAt'_add, valAt'_mul, valAt'_comp]
    rw [valAt'_res _ _ f h, valAt'_res _ _ f' h]
  res W W' e hW f := by
    have h : z ∈ dom u m (W' ⊓ W₀) := (dom_inf u m).2 ⟨hW, hz⟩
    rw [ev_eq u m hd (inf_le_left.trans e) inf_le_right h f, ev, res_res]

theorem ev_base (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} (hz : z ∈ dom u m W₀) (r : R) :
    ev u m W₀ d z ⊤ (constFn p ⊤ r) = D r := by
  rw [ev_eq u m hd le_top le_rfl hz, res_const, hd.base _ le_rfl]
  exact valAt'_constFn _ _ (ex_hom u z) _ _ hz

theorem ev_hol (W : X.Opens) (f : Γ(X, W)) :
    DifferentiableOn ℂ (fun z => ev u m W₀ d z W f) (dom u m (W ⊓ W₀)) := val_hol u m _ _

theorem ev_per (l : u.Λ) (z : Fin g → ℂ) : ev u m W₀ d (z + l) = ev u m W₀ d z := by
  funext W f
  simp only [ev, ex_per]

theorem fderiv_field_hol (W : X.Opens) (f : Γ(X, W)) {S : Set (Fin g → ℂ)} (hS : S ⊆ dom u m W)
    (h : Fin g → (Fin g → ℂ) → ℂ) (hh : ∀ a, DifferentiableOn ℂ (h a) S) :
    DifferentiableOn ℂ (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) S := by
  have e : (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) =
      fun z => ∑ a, h a z * fderiv ℂ (fn u m W f) z (Pi.single a 1) := by
    funext z
    conv_lhs => rw [show (fun a => h a z) = ∑ a, h a z • (Pi.single a 1 : Fin g → ℂ) from
      (pi_eq_sum_univ' _)]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [e]
  refine DifferentiableOn.fun_sum fun a _ => (hh a).mul ?_
  exact (((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ _ (dom_open u m W)).2 (fn_hol u m W f)).2 _).mono hS

theorem exists_affine_dom (z : Fin g → ℂ) : ∃ i : X.affineOpens, z ∈ dom u m i.1 := by
  obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  exact ⟨⟨W, hW⟩, (top_le_preimage_iff_mem _ _).2 hx⟩

theorem exists_ksRel : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D, IsDer x₀ D → ∃ Θ s, KSRel u p m D Θ s := by
  intro P₀ u Hm χ hu R _ x₀ X p m hp hm D hD
  choose d hd using fun i : X.affineOpens => GlobalTheory.T.exists_localDerivationAlongFibre_of_smooth R x₀ _ X P₀.A.hom p m D i.1 hp hm.w hD i.2
  choose c hc using fun i j : X.affineOpens =>
    GlobalTheory.KS.locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hd i) (hd j))
  let C : X.affineOpens → X.affineOpens → (Fin P₀.g → ℂ) → Fin P₀.g → ℂ :=
    fun i j z a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (c i j a)
  have hC : ∀ i j z W f, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m W →
      ev u m i.1 (d i) z W f - ev u m j.1 (d j) z W f = fderiv ℂ (fn u m W f) z (C i j z) := by
    intro i j z W f hi hj hW
    have h : z ∈ dom u m (W ⊓ (i.1 ⊓ j.1)) := (dom_inf u m).2 ⟨hW, (dom_inf u m).2 ⟨hi, hj⟩⟩
    rw [ev_eq u m (hd i) inf_le_left (inf_le_right.trans inf_le_left) h,
      ev_eq u m (hd j) inf_le_left (inf_le_right.trans inf_le_right) h, ← valAt'_sub,
      hc i j _ inf_le_right _ z h, fderiv_res u m _ _ h]
  have hco : ∀ i j k z, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m k.1 → C i j z + C j k z = C i k z := by
    intro i j k z hi hj hk
    refine (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hu R x₀ X p m hp hm z _ (ptDer_fderiv u m z (C i k z))
      (fun r => fderiv_const_eq u m hm.w r z _)).unique (fun W f hW => ?_) (fun _ _ _ => rfl)
    rw [map_add, ← hC i j z W f hi hj hW, ← hC j k z W f hj hk hW, ← hC i k z W f hi hk hW]
    ring
  choose t h hh hch using fun a : Fin P₀.g =>
    GlobalTheory.holomorphic_periodic_cocycle_coboundary P₀.g u.Λ u.discrete u.full X.affineOpens (fun i => dom u m i.1)
      (fun i j z => C i j z a) (fun i => dom_open u m _) (fun i l z hz => (dom_per u m l _ z).2 hz)
      (exists_affine_dom u m)
      (fun i j => (val_hol u m _ (c i j a)).mono fun z hz => (dom_inf u m).2 hz)
      (fun i j l z _ => by simp only [C, ex_per])
      (fun i j k z hz => congrFun (hco i j k z hz.1.1 hz.1.2 hz.2) a)
  choose κ hκ using exists_affine_dom u m
  let s : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ := fun z W f =>
    ev u m (κ z).1 (d (κ z)) z W f + fderiv ℂ (fn u m W f) z (fun a => h a (κ z) z)
  have hs : ∀ j z W f, z ∈ dom u m j.1 → z ∈ dom u m W →
      s z W f = ev u m j.1 (d j) z W f + fderiv ℂ (fn u m W f) z (fun a => h a j z) := by
    intro j z W f hj hW
    have e₁ := hC (κ z) j z W f (hκ z) hj hW
    have e₂ : C (κ z) j z = (fun a => h a j z) - fun a => h a (κ z) z :=
      funext fun a => hch a (κ z) j z ⟨hκ z, hj⟩
    rw [e₂, map_sub] at e₁
    simp only [s]
    linear_combination e₁
  refine ⟨Matrix.of t, s, fun z => ptDer_add (ptDer_ev u m (hd _) (hκ z)) (ptDer_fderiv u m z _), fun z r => ?_,
    fun W f z hz => ?_, fun l W f z hz => ?_⟩
  · simp only [s]
    rw [ev_base u m (hd _) (hκ z), fderiv_const_eq u m hm.w, add_zero]
  · have hz' : z ∈ dom u m (W ⊓ (κ z).1) := (dom_inf u m).2 ⟨hz, hκ z⟩
    have hn := (dom_open u m _).mem_nhds hz'
    have h₁ := (ev_hol u m (W₀ := (κ z).1) (d := d (κ z)) W f).add
      (fderiv_field_hol u m W f (S := dom u m (W ⊓ (κ z).1)) (fun y hy => ((dom_inf u m).1 hy).1)
        (fun a => h a (κ z)) fun a => (hh a (κ z)).1.mono fun y hy => ((dom_inf u m).1 hy).2)
    refine ((h₁.congr fun y hy => ?_).differentiableAt hn).differentiableWithinAt
    exact hs (κ z) y W f ((dom_inf u m).1 hy).2 ((dom_inf u m).1 hy).1
  · rw [hs (κ z) (z + l) W f ((dom_per u m l _ z).2 (hκ z)) ((dom_per u m l _ z).2 hz), ev_per, fderiv_per]
    have e : (fun a => h a (κ z) (z + l)) = (fun a => h a (κ z) z) + (Matrix.of t).mulVec (star (l : Fin P₀.g → ℂ)) :=
      funext fun a => (hh a (κ z)).2 l z (hκ z)
    rw [e, map_add]
    simp only [s]
    ring

end GlobalTheory.KS.Exist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_extends_from_genericFibre_valuationRing : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → Triv (M.pull j) → Triv M := by
  first | exact @GlobalTheory.ValGenExtend.triv_of_triv_generic | exact GlobalTheory.ValGenExtend.triv_of_triv_generic | (intros; apply GlobalTheory.ValGenExtend.triv_of_triv_generic <;> assumption)
end

