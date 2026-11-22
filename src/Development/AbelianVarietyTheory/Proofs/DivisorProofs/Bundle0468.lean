import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemRightTranslateMemIdentityComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_mem_and_rightTranslate_mem_of_mem_identityComponent :
    ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), (η[G]).left (IsLocalRing.closedPoint k) ∈ U → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → ∃ z : G.left, z ∈ U ∧ (𝟙 G * (toUnit G ≫ y) : G ⟶ G).left z ∈ U := by
  intro k _ G _ hs U y hU hy
  set e : G.left := (η[G]).left (IsLocalRing.closedPoint k) with he
  have hirr : IsIrreducible (connectedComponent e) := by
    have h := (GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth k G.left G.hom (η[G]).left hs (Over.w (η[G]))).2
    have hsub : ∀ a : Spec (CommRingCat.of k), a = IsLocalRing.closedPoint k := fun a =>
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    convert h using 1
    ext x
    have h1 : (G.hom ⁻¹' {G.hom x} : Set G.left) = Set.univ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact (hsub _).trans (hsub _).symm
    simp only [Set.mem_ofPred_eq]
    rw [h1, connectedComponentIn_univ, hsub (G.hom x)]
  let T : G ⟶ G := 𝟙 G * (toUnit G ≫ y)
  have hT : (y ≫ ι[G]) ≫ T = η[G] := by
    have h1 : (y ≫ ι[G]) ≫ T = (y ≫ ι[G]) * y := by
      simp only [T]
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, toUnit_unit,
        Category.id_comp]
    rw [h1]
    have h2 : (y ≫ ι[G]) = y⁻¹ := rfl
    rw [h2, inv_mul_cancel, Hom.one_def, toUnit_unit, Category.id_comp]
  have hιe : (ι[G]).left e = e := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    have h2 := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) this
    exact h2
  have hyi : (ι[G]).left (y.left (IsLocalRing.closedPoint k)) ∈ connectedComponent e := by
    have hc := (ι[G]).left.continuous.image_connectedComponent_subset e
    rw [hιe] at hc
    exact hc ⟨_, hy, rfl⟩
  have hTy : T.left ((ι[G]).left (y.left (IsLocalRing.closedPoint k))) = e := by
    have h2 := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) hT
    exact h2
  obtain ⟨z, -, hz1, hz2⟩ := hirr.isPreirreducible (U : Set G.left) (T.left ⁻¹' (U : Set G.left))
    U.isOpen (U.isOpen.preimage T.left.continuous) ⟨e, mem_connectedComponent, hU⟩
    ⟨_, hyi, by rw [Set.mem_preimage, hTy]; exact hU⟩
  exact ⟨z, hz1, hz2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCommonZeroOfIsHomogeneous
section
open IsLocalRing

namespace GlobalTheory

theorem exists_ne_zero_common_zero_of_isHomogeneous :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k),
      (∀ i, ∃ d, 0 < d ∧ (f i).IsHomogeneous d) → r < n →
        ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r f hf hrn
  by_contra hcon
  push Not at hcon
  set I : Ideal (MvPolynomial (Fin n) k) := Ideal.span (Set.range f) with hIdef
  set M : Ideal (MvPolynomial (Fin n) k) :=
    MvPolynomial.vanishingIdeal k ({(0 : Fin n → k)} : Set (Fin n → k)) with hMdef
  have hMmax : M.IsMaximal := inferInstance

  have hf0 : ∀ i, MvPolynomial.eval (0 : Fin n → k) (f i) = 0 := by
    intro i
    obtain ⟨d, hd, hh⟩ := hf i
    rw [MvPolynomial.eval_zero]
    rw [MvPolynomial.constantCoeff_eq]
    apply hh.coeff_eq_zero
    simp
    omega
  have hIM : I ≤ M := by
    rw [hIdef, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hMdef, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hf0 i

  have hZ : MvPolynomial.zeroLocus k I ⊆ ({(0 : Fin n → k)} : Set (Fin n → k)) := by
    intro x hx
    by_contra hx0
    obtain ⟨i, hi⟩ := hcon x hx0
    apply hi
    have := hx (f i) (Ideal.subset_span ⟨i, rfl⟩)
    exact this
  have hMrad : M ≤ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I]
    exact MvPolynomial.vanishingIdeal_anti_mono hZ
  have hXM : Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))
      ≤ M := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hMdef, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  have hItop : I ≠ ⊤ := fun h => hMmax.ne_top (top_le_iff.mp (h ▸ hIM))
  have hrad : I.radical.height = I.height := by
    rw [Ideal.height_eq_inf_minimalPrimes, Ideal.height_eq_inf_minimalPrimes,
      Ideal.radical_minimalPrimes]
  have hfin : (I.spanFinrank : ℕ∞) ≤ r := by
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := MvPolynomial (Fin n) k)
      (Set.finite_range f)
    have h2 : (Set.range f).ncard ≤ r := by
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp [Set.ncard_univ]
    exact_mod_cast h1.trans h2
  have key : (n : ℕ∞) ≤ r :=
    (GlobalTheory.le_height_span_range_X_mvPolynomial k n).trans <| (Ideal.height_mono hXM).trans <| (Ideal.height_mono hMrad).trans <|
      hrad.le.trans <| (Ideal.height_le_spanFinrank I hItop).trans hfin
  have : n ≤ r := by exact_mod_cast key
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneFormsCocycleRestrictSubCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem exists_cocycle_restrict_sub_eq_coboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict (FormExt.omExt F) G).pull1 → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) := by
  intro R _ C _ C' _ F G hsurj β' hβ'
  let f' : Z1 (G ⋙ omExt F) := ⟨fun t t' a ↦ (TrivSqZeroExt.inr (β' t t' a) : (omExt F).obj (G.obj t')),
    fun t t' t'' a b ↦ by
      apply TrivSqZeroExt.ext
      · show (0 : F.obj (G.obj t'')) = (extMap F (G.map b) (TrivSqZeroExt.inr (β' t t' a))).fst + 0
        rw [fst_extMap]; simp
      · show β' t t'' (a ≫ b) = (extMap F (G.map b) (TrivSqZeroExt.inr (β' t t' a))).snd + β' t' t'' b
        rw [snd_extMap, hβ']; rfl⟩
  obtain ⟨h0, hh⟩ := hsurj (H1.mk _ f')
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ h0
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hh
  obtain ⟨g, hg⟩ := hh
  refine ⟨fun T T' φ ↦ (f.1 T T' φ).snd, fun T T' T'' φ ψ ↦ ?_, fun t ↦ (g t).snd, fun t t' a ↦ ?_⟩
  · have e := congrArg TrivSqZeroExt.snd (Z1.comp f φ ψ)
    have e2 : TrivSqZeroExt.snd (mp (omExt F) ψ (f.1 T T' φ) + f.1 T' T'' ψ) =
        p1 F ψ (f.1 T T' φ).snd + (f.1 T' T'' ψ).snd := by
      show (extMap F ψ (f.1 T T' φ)).snd + (f.1 T' T'' ψ).snd = _
      exact congrArg (· + (f.1 T' T'' ψ).snd) (snd_extMap F ψ (f.1 T T' φ))
    exact e.trans e2
  · have e := congrArg TrivSqZeroExt.snd (congrFun (congrFun (congrFun hg t) t') a)
    have e2 : (g t').snd - p1 F (G.map a) (g t).snd = (f.1 _ _ (G.map a)).snd - β' t t' a :=
      calc (g t').snd - p1 F (G.map a) (g t).snd
          = (g t').snd - (extMap F (G.map a) (g t)).snd :=
            congrArg (fun z ↦ (g t').snd - z) (snd_extMap F (G.map a) (g t)).symm
        _ = TrivSqZeroExt.snd (d0 (G ⋙ omExt F) g t t' a) := rfl
        _ = _ := e
        _ = (f.1 _ _ (G.map a)).snd - β' t t' a := rfl
    exact e2.symm

end GlobalTheory.CechDR.FormExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankTwoBasisModN
section
open NumberField

namespace GlobalTheory.LatticeModN

theorem exists_gen_modN : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M], Module.finrank ℤ M = 2 * Module.finrank ℚ F → ∀ N : ℕ, 1 ≤ N → ∃ x : Fin 2 → M, (∀ m : M, ∃ (a b : 𝓞 F) (m' : M), m = a • x 0 + b • x 1 + N • m') ∧ ∀ a b : 𝓞 F, (∃ m' : M, a • x 0 + b • x 1 = N • m') → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  intro F _ _ M _ _ _ _ hrk N hN
  rcases Nat.lt_or_ge N 2 with h1 | h2
  · obtain rfl : N = 1 := by omega
    refine ⟨0, fun m => ⟨0, 0, m, by simp⟩, fun a b _ => ⟨by simp, by simp⟩⟩
  obtain ⟨r, x, hli, c, hc0, hcop, hspan⟩ := GlobalTheory.T.exists_independent_basis_coprime F M N h2
  have hr := GlobalTheory.T.finrank_eq_rank_mul_degree F M r x hli c hc0 hspan
  have hf : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hr2 : r = 2 := by
    rw [hrk] at hr
    exact (Nat.eq_of_mul_eq_mul_right hf hr).symm
  subst hr2
  obtain ⟨u, v, huv⟩ := hcop
  have hNs : ∀ y : M, (N : 𝓞 F) • y = N • y := fun y => Nat.cast_smul_eq_nsmul (𝓞 F) N y
  refine ⟨x, fun m => ?_, fun a b ⟨m', hm'⟩ => ?_⟩
  · obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).1 (hspan m)
    rw [Fin.sum_univ_two] at hg
    refine ⟨u * g 0, u * g 1, v • m, ?_⟩
    calc m = (1 : 𝓞 F) • m := (one_smul _ _).symm
      _ = u • (c • m) + (N : 𝓞 F) • (v • m) := by rw [← huv, add_smul, mul_smul, mul_comm v, mul_smul]
      _ = _ := by rw [← hg, hNs, smul_add, mul_smul, mul_smul]
  · obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).1 (hspan m')
    rw [Fin.sum_univ_two] at hg
    have key : (c * a - N * g 0) • x 0 + (c * b - N * g 1) • x 1 = 0 := by
      have e1 : c • (a • x 0 + b • x 1) = (N : 𝓞 F) • (c • m') := by
        rw [hm', ← hNs, smul_comm]
      rw [← hg, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul] at e1
      rw [sub_smul, sub_smul]
      linear_combination (norm := module) e1
    have hz := Fintype.linearIndependent_iff.1 hli ![c * a - N * g 0, c * b - N * g 1]
      (by simpa [Fin.sum_univ_two] using key)
    have ha : c * a = N * g 0 := sub_eq_zero.1 (hz 0)
    have hb : c * b = N * g 1 := sub_eq_zero.1 (hz 1)
    refine ⟨⟨u * g 0 + v * a, ?_⟩, ⟨u * g 1 + v * b, ?_⟩⟩
    · calc a = (u * c + v * N) * a := by rw [huv, one_mul]
        _ = u * (c * a) + N * (v * a) := by ring
        _ = _ := by rw [ha]; ring
    · calc b = (u * c + v * N) * b := by rw [huv, one_mul]
        _ = u * (c * b) + N * (v * b) := by ring
        _ = _ := by rw [hb]; ring

end GlobalTheory.LatticeModN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiMapOfTensorPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section

namespace GlobalTheory.EtC.SemiTens

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.map f z) = Sec.map f (Sec.res g z) := by
  have := congrArg (fun k => k.hom z) (f.hom.naturality g.op)
  simpa using this.symm

theorem map_zero' {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (z : Sec F U) :
    Sec.map (0 : F ⟶ G) z = 0 := by
  first
  | rfl
  | (show ((0 : F ⟶ G).hom.app (op U)).hom z = 0
     rw [Sheaf.Hom.zero_hom]; rfl)
  | (simp [Sec.map, Sheaf.zero_val])

variable {Q : ℕ} {R : Type} [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R}

def pairHom (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec (I.X s) U →+ Sec (J.X t) U →+ Sec (K'.X w) U :=
  AddMonoidHom.mk' (fun a => ((ν.mul U s t w h (ρ₁.app U s a)).toAddMonoidHom).comp (ρ₂.app U t))
    (fun a₁ a₂ => by ext b; simp)

theorem pairHom_smul (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) (r : ULift.{1} (ZMod Q)) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    pairHom ν ρ₁ ρ₂ U s t w h (r • a) b = pairHom ν ρ₁ ρ₂ U s t w h a (r • b) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ULift.{1} (ZMod Q)) = r :=
    ⟨(r.down.cast : ℤ), ULift.ext _ _ (by change ((r.down.cast : ℤ) : ZMod Q) = r.down; exact ZMod.intCast_zmod_cast _)⟩
  simp [pairHom, Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply]

def bmap (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →+ Sec (K'.X w) U := by
  classical
  exact DirectSum.toAddMonoid fun p =>
    TensorProduct.liftAddHom (pairHom ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2) (pairHom_smul ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2)

theorem bmap_of (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    bmap ν ρ₁ ρ₂ U w (DirectSum.of _ p (a ⊗ₜ b)) = ν.mul U p.1.1 p.1.2 w p.2 (ρ₁.app U _ a) (ρ₂.app U _ b) := by
  unfold bmap
  rw [DirectSum.toAddMonoid_of]
  simp [pairHom]

theorem lift_of (τ : Pair I J T) (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    τ.lift U w (DirectSum.of _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.toModule_lof]
  simp

theorem tensRes_of {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p (a ⊗ₜ b)) = DirectSum.of _ p (Sec.res g a ⊗ₜ Sec.res g b) := by
  unfold Tens.res
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.lmap_lof]
  simp [DirectSum.lof_eq_of]

theorem bmap_nat (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (bmap ν ρ₁ ρ₂ U w x) = bmap ν ρ₁ ρ₂ V w (Tens.res g w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [bmap_of, tensRes_of, bmap_of, ν.nat, ρ₁.nat, ρ₂.nat]
    | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add] using e
  | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add] using e

end GlobalTheory.EtC.SemiTens

namespace GlobalTheory.EtC

open SemiTens in

theorem semiMap_of_tensorPair : ∀ (Q : ℕ) (R : Type) [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R} (τ : Pair I J T),
    τ.IsTensor → ∀ (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J'), ∃ σ : SemiMap T K',
    ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
  intro Q R _ I J T I' J' K' τ hτ ν ρ₁ ρ₂
  have H := fun w => GlobalTheory.T.sheafComplexPairing_tensor_universal_property (ZMod Q) R τ hτ w (K'.X w) (fun U => bmap ν ρ₁ ρ₂ U w)
    (fun V U g x => bmap_nat ν ρ₁ ρ₂ g w x)
  choose φ hnat hlift using H
  have hmul : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      φ w U (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
    intro U s t w h a b
    have := hlift w U (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))
    rw [lift_of, bmap_of] at this
    exact this
  have key : ∀ (V : Scheme.{0}) (s : ℤ) (x : Tens I J V s),
      Sec.map (K'.d s (s + 1)) (bmap ν ρ₁ ρ₂ V s x) = φ (s + 1) V (Sec.map (T.d s (s + 1)) (τ.lift V s x)) := by
    intro V s x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        obtain ⟨⟨s₁, t₁⟩, hp⟩ := p
        rw [bmap_of, lift_of, ν.leibniz, τ.leibniz, map_add, Units.smul_def, Units.smul_def, map_zsmul, hmul, hmul,
          ρ₁.comm, ρ₂.comm]
      | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add] using e
    | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add] using e
  refine ⟨⟨fun U w => φ w U, fun g w a => hnat w _ _ g a, ?_⟩, hmul⟩
  intro U s t y
  by_cases hst : (ComplexShape.up ℤ).Rel s t
  · have ht : t = s + 1 := hst.symm
    subst ht
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R (K'.X (s + 1)) U).1
    obtain ⟨S, hS, hP⟩ := hτ.1 U s y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    rw [res_map, hnat, ← hx, hlift, key, hnat, res_map, ← hx]
  · rw [T.shape s t hst, K'.shape s t hst, map_zero', map_zero', map_zero]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemidirectCharacterExtOfStableStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semidirect_character_ext_of_stable : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∃ Z : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ Z ∧ ∀ g, Z (inl g) = Y g := by
  first | (exact @GlobalTheory.StableExt.exists_ext) | (exact GlobalTheory.StableExt.exists_ext) | (intros; apply GlobalTheory.StableExt.exists_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateTwistMulDegreeZeroHom
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem Sec.res_map_of_sheaf_morphism {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have h := congrArg (fun h => h.hom x) (f.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem Sec.map_nsmul_of_sheaf_morphism {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map f (n • x) = n • Sec.map f x := map_nsmul (f.hom.app (op U)).hom n x

theorem nsmul_eq_of_natCast_eq_zmod_ulift_module {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {m n : ℕ}
    (h : (m : ZMod q) = (n : ZMod q)) (x : M) : m • x = n • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) m x, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) n x]
  congr 1
  apply ULift.ext
  simpa using h

theorem twist_mul_map : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)}
    (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), ∃ φ : tw q k ⟶ K.X 0, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) := by
  intro q _ i j k hk K τ
  obtain ⟨-, -, -, h4i, h5i, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
  obtain ⟨-, -, -, h4j, h5j, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q j
  obtain ⟨-, -, -, -, -, h6⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q k
  let e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (K.X 0) U := fun U ζ =>
    τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))
  have hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    simp only [e]
    rw [τ.nat, Sec.res_map_of_sheaf_morphism, Sec.res_map_of_sheaf_morphism, h4i, h4j]
  have hrel : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ k : (ZMod q)ˣ) : ZMod q).val • e U ζ := by
    intro U ζ ξ a h
    simp only [e]
    rw [h5i U ζ ξ a h, h5j U ζ ξ a h, Sec.map_nsmul_of_sheaf_morphism, Sec.map_nsmul_of_sheaf_morphism, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul]
    apply nsmul_eq_of_natCast_eq_zmod_ulift_module (q := q)
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id,
      ← hk, zpow_add, Units.val_mul, mul_comm]
  obtain ⟨φ, hφ, -⟩ := h6 (K.X 0) e hnat hrel
  exact ⟨φ, hφ⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAffineLineMorphismToProperAcrossPoint
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffineLineExt

open Polynomial

theorem isPrincipalIdealRing_away {R : Type} [CommRing R] [IsPrincipalIdealRing R] (r : R) :
    IsPrincipalIdealRing (Localization.Away r) := ⟨fun J => by
  rw [← IsLocalization.map_under (Submonoid.powers r) (Localization.Away r) J]
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (J.under R)).principal
  rw [ha]
  exact ⟨⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]⟩⟩⟩

theorem extend : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  intro k _ B _ _ P c hP u hu
  have hQ0 : P * (X - C c) ≠ 0 := mul_ne_zero hP (X_sub_C_ne_zero c)
  haveI : IsDomain (Localization.Away P) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hP)
  haveI : IsDomain (Localization.Away (P * (X - C c))) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hQ0)
  haveI : IsPrincipalIdealRing (Localization.Away P) := isPrincipalIdealRing_away P
  have hφ : ∀ a : k[X], IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c) (algebraMap k[X] (Localization.Away P) a) =
      algebraMap k[X] (Localization.Away (P * (X - C c))) a :=
    IsLocalization.Away.awayToAwayRight_eq P (X - C c)
  have hcomp : spMap (algebraMap k[X] (Localization.Away (P * (X - C c)))) =
      spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  haveI : IsOpenImmersion (spMap (algebraMap k[X] (Localization.Away P))) :=
    IsOpenImmersion.of_isLocalization P
  haveI : IsOpenImmersion (spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P))) := by
    rw [← hcomp]
    exact IsOpenImmersion.of_isLocalization (P * (X - C c))
  haveI := IsOpenImmersion.of_comp (spMap (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c)))
    (spMap (algebraMap k[X] (Localization.Away P)))
  haveI : B.left.IsSeparated := ⟨by
    rw [show terminal.from B.left = B.hom ≫ terminal.from (Sp k) from terminal.hom_ext _ _]
    infer_instance⟩
  have hu' : u ≫ B.hom = spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫ spMap (algebraMap k (Localization.Away P)) := by
    rw [hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away P), hφ,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, h1, h2⟩ := TorusConst.exists_extension (Z := Sp (Localization.Away P))
    (fun x => TorusConst.valuationRing_stalk (Localization.Away P) x) _
    (spMap (algebraMap k (Localization.Away P))) B.hom u hu'
  exact ⟨g, h2, h1⟩

end GlobalTheory.AffineLineExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive : ∀ (q : ℕ) [NeZero q], (∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk γ = c1 q L ∧ (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧ (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) → w ^ q = lineUnit L (x.sub 1 1 (by omega)) → ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' → pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧ ∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E → (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M := by
  first | (exact @GlobalTheory.EtC.firstChernClassTateTwist_cocycle_naturality_additivity) | (exact GlobalTheory.EtC.firstChernClassTateTwist_cocycle_naturality_additivity) | (intros; apply GlobalTheory.EtC.firstChernClassTateTwist_cocycle_naturality_additivity  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH1BijectiveStatement
section
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forget_positive_h1_bijective : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), K.M1.Ac0 → K.M1.Ac1 → K.M2.Ac0 → Function.Bijective K.fnMap.h1 := by
  first | exact @GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | exact GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | (intros; apply GlobalTheory.CxCoh.Cx.fnMap_h1_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH2BijectiveStatement
section
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forget_positive_h2_bijective : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), K.M1.Ac1 → K.M1.Ac2 → K.M2.Ac0 → K.M2.Ac1 → K.M3.Ac0 → Function.Bijective K.fnMap.h2 := by
  first | exact @GlobalTheory.CxCoh.fnMap_h2_bijective | exact GlobalTheory.CxCoh.fnMap_h2_bijective | (intros; apply GlobalTheory.CxCoh.fnMap_h2_bijective <;> assumption)
end

