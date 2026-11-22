import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0033
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducible
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLCRes
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapSpecProof

variable {R : Type} [CommRing R]

theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  delta GlobalTheory.EtC.Sec.res
  rw [op_comp, Functor.map_comp]
  rfl

theorem primRes_comp {q : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    primRes (k ≫ g) ζ = primRes k (primRes g ζ) := by
  apply Subtype.ext
  delta CrystallineSemistableComparison.E.primRes
  rfl

theorem sec_subsingleton (hL : LcCover) {U : Scheme.{0}} [IsEmpty U] (G : Shv R) :
    Subsingleton (Sec G U) := by
  let f0 : LocallyConstant U Empty :=
    ⟨fun u => isEmptyElim u, fun s => by
      convert isOpen_empty
      ext u
      exact isEmptyElim u⟩
  obtain ⟨W, j, -, -, -, hglue⟩ := hL U Empty f0
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => a.elim)
  exact ⟨fun x x' => (hz x (fun a => a.elim)).trans (hz x' (fun a => a.elim)).symm⟩

theorem sec_ext (hL : LcCover) {ι : Type} {U : Scheme.{0}} (f : LocallyConstant U ι) (G : Shv R)
    (x y : Sec G U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (a : ι), (∀ v : V, f (g v) = a) → Sec.res g x = Sec.res g y) :
    x = y := by
  obtain ⟨W, j, hWf, -, -, hglue⟩ := hL U ι f
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => Sec.res (j a) x)
  exact (hz x (fun a => rfl)).trans (hz y (fun a => (h (W a) (j a) a (hWf a)).symm)).symm

variable {q : ℕ} {i : ℤ}

theorem isLC_unique (hL : LcCover) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x y : Sec (tw q i) U} (hx : IsLC i ζ f x) (hy : IsLC i ζ f y) :
    x = y := by
  refine sec_ext hL f _ x y fun V g a hga => ?_
  delta CrystallineSemistableComparison.E.IsLC at hx hy
  rw [hx V g a hga, hy V g a hga]

theorem isLC_exists (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : LocallyConstant U (ZMod q)) : ∃ x : Sec (tw q i) U, IsLC i ζ f x := by
  delta CrystallineSemistableComparison.E.IsLC
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  obtain ⟨W, j, -, hfac, -, hglue⟩ := hL U (ZMod q) f
  obtain ⟨x, hx, -⟩ := hglue (ZMod q) (tw q i)
    (fun a => (⟨a⟩ : ULift (ZMod q)) • twGen i (primRes (j a) ζ))
  refine ⟨x, fun V g a ha => ?_⟩
  obtain ⟨k, rfl⟩ := hfac V g a ha
  rw [res_comp, hx a, hres_smul, ((hR q i (W a) (primRes (j a) ζ)).1 V k).1, ← primRes_comp]

theorem isLC_add (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f f' : LocallyConstant U (ZMod q)} {x x' : Sec (tw q i) U} (hx : IsLC i ζ f x)
    (hx' : IsLC i ζ f' x') : IsLC i ζ (f + f') (x + x') := by
  delta CrystallineSemistableComparison.E.IsLC at hx hx' ⊢
  intro V g a ha
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  have hcont : Continuous (fun v : V => g v) := g.continuous
  let F2 : LocallyConstant V (ZMod q × ZMod q) :=
    ⟨fun v => (f (g v), f' (g v)), IsLocallyConstant.comp₂ (f.isLocallyConstant.comp_continuous hcont)
      (f'.isLocallyConstant.comp_continuous hcont) Prod.mk⟩
  refine sec_ext hL F2 _ _ _ fun V' g' b hb => ?_
  rcases isEmpty_or_nonempty V' with hV | ⟨⟨v⟩⟩
  · haveI := sec_subsingleton hL (U := V') (tw q i)
    exact Subsingleton.elim _ _
  have hb1 : ∀ v, f ((g' ≫ g) v) = b.1 := fun v => congrArg Prod.fst (hb v)
  have hb2 : ∀ v, f' ((g' ≫ g) v) = b.2 := fun v => congrArg Prod.snd (hb v)
  have hres_add : ∀ (y y' : Sec (tw q i) U),
      Sec.res (g' ≫ g) (y + y') = Sec.res (g' ≫ g) y + Sec.res (g' ≫ g) y' := fun y y' => by
    delta GlobalTheory.EtC.Sec.res
    exact map_add _ y y'
  have hab : a = b.1 + b.2 := by
    rw [← ha (g' v), ← hb1 v, ← hb2 v]
    rfl
  rw [← res_comp, hres_add, hx V' (g' ≫ g) b.1 hb1, hx' V' (g' ≫ g) b.2 hb2, ← add_smul, hres_smul,
    ((hR q i V (primRes g ζ)).1 V' g').1, ← primRes_comp, hab]
  rfl

theorem isLC_res {U V : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x : Sec (tw q i) U} (hx : IsLC i ζ f x) (g : V ⟶ U) :
    IsLC i (primRes g ζ) (lcRes q g f) (Sec.res g x) := by
  delta CrystallineSemistableComparison.E.IsLC at hx ⊢
  intro W h a ha
  rw [← res_comp, hx W (h ≫ g) a ?_, primRes_comp]
  intro w
  exact ha w

theorem kapSpec : LcCover → RepRoot → KapSpec := by
  intro hL hR q i U ζ f
  have hk : ∀ {U' : Scheme.{0}} (ζ' : Prim q Γ(U', ⊤)) (f' : LocallyConstant U' (ZMod q)),
      IsLC i ζ' f' (kap i ζ' f') := by
    intro U' ζ' f'
    have hex : ∃ κ : LocallyConstant U' (ZMod q) →+ Sec (tw q i) U', ∀ f'', IsLC i ζ' f'' (κ f'') := by
      choose c hc using fun f'' : LocallyConstant U' (ZMod q) => isLC_exists hL hR (i := i) ζ' f''
      refine ⟨{ toFun := c, map_zero' := ?_, map_add' := fun a b => ?_ }, hc⟩
      · have h := isLC_unique hL (hc (0 + 0)) (isLC_add hL hR (hc 0) (hc 0))
        simpa using h
      · exact isLC_unique hL (hc (a + b)) (isLC_add hL hR (hc a) (hc b))
    delta CrystallineSemistableComparison.E.kap
    exact GlobalTheory.EtC.pick_spec hex f'
  refine ⟨hk ζ f, fun x hx => isLC_unique hL hx (hk ζ f), fun V g => ?_⟩
  exact isLC_unique hL (isLC_res (hk ζ f) g) (hk _ _)

end GlobalTheory.CompanionTheory.KapSpecProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneSubPow
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimAlgProof

open Polynomial

theorem exists_universal (q : ℕ) [NeZero q] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (ξ : R), IsPrimitiveRoot ξ q ∧
      ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
        ∃ φ : R →+* A, φ ξ = z := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hlift : ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
      ∃ φ : AdjoinRoot (cyclotomic q ℤ) →+* A, φ (AdjoinRoot.root _) = z := by
    intro A _ z hz
    have h : (cyclotomic q ℤ).eval₂ (Int.castRingHom A) z = 0 := by
      rw [aeval_def] at hz
      simpa [eq_intCast] using hz
    exact ⟨AdjoinRoot.lift _ z h, AdjoinRoot.lift_root h⟩
  haveI hdom : IsDomain (AdjoinRoot (cyclotomic q ℤ)) :=
    AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible hq).prime
  refine ⟨AdjoinRoot (cyclotomic q ℤ), inferInstance, hdom, AdjoinRoot.root _, ?_, hlift⟩
  obtain ⟨ψ, hψ⟩ := hlift ℂ (Complex.exp (2 * Real.pi * Complex.I / q)) (by
    have hp := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
    have : IsRoot (cyclotomic q ℂ) (Complex.exp (2 * Real.pi * Complex.I / q)) :=
      (isRoot_cyclotomic_iff).2 hp
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact this)
  haveI : NeZero ((q : ℕ) : AdjoinRoot (cyclotomic q ℤ)) := ⟨fun h0 => by
    have := congrArg ψ h0
    rw [map_natCast, map_zero] at this
    exact NeZero.ne q (by exact_mod_cast this)⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  have h := AdjoinRoot.eval₂_root (cyclotomic q ℤ)
  rw [eval₂_eq_eval_map, map_cyclotomic] at h
  exact h

theorem X_pow_sub_one_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    (X ^ q - 1 : R[X]) = ∏ a : ZMod q, (X - C (ξ ^ a.val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [X_pow_sub_one_eq_prod hq hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ a.val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_nthRootsFinset hq]
    rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  · intro a _ b _ h
    exact ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)
  · intro μ hμ
    rw [mem_nthRootsFinset hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ
    exact ⟨(i : ZMod q), Finset.mem_univ _, by rw [ZMod.val_cast_of_lt hi]⟩
  · intro a _
    rfl

theorem cyclotomic_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    cyclotomic q R = ∏ a : (ZMod q)ˣ, (X - C (ξ ^ (a : ZMod q).val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ (a : ZMod q).val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_primitiveRoots hq]
    exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  · intro μ hμ
    rw [mem_primitiveRoots hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    have hc : Nat.Coprime i q := (hξ.pow_iff_coprime hq i).1 hμ
    refine ⟨ZMod.unitOfCoprime i hc, Finset.mem_univ _, ?_⟩
    simp only [ZMod.coe_unitOfCoprime]
    rw [ZMod.val_cast_of_lt hi]
  · intro a _
    rfl

theorem isUnit_one_sub_pow {R A : Type} [CommRing R] [IsDomain R] [CommRing A] (n : ℕ) {ξ : R}
    (hξ : IsPrimitiveRoot ξ (n + 1)) (φ : R →+* A) (hu : IsUnit ((n + 1 : ℕ) : A))
    (k : ℕ) (hk : k < n) : IsUnit (1 - φ ξ ^ (k + 1)) := by
  have h := congrArg φ hξ.prod_one_sub_pow_eq_order
  rw [map_prod] at h
  have hn : φ ((n : R) + 1) = ((n + 1 : ℕ) : A) := by simp
  have hd : φ (1 - ξ ^ (k + 1)) ∣ ∏ i ∈ Finset.range n, φ (1 - ξ ^ (i + 1)) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk)
  rw [h, hn] at hd
  have := isUnit_of_dvd_unit hd hu
  simpa using this

theorem primAlg : CrystallineSemistableComparison.E.PrimAlg := by
  intro q _ A _ ζ
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨R, _, _, ξ, hξ, hl⟩ := exists_universal q
  obtain ⟨φ, hφ⟩ := hl A ζ.1 ζ.2.2
  have hpow : ζ.1 ^ q = 1 := by rw [← hφ, ← map_pow, hξ.pow_eq_one, map_one]
  have hζu : IsUnit ζ.1 := by
    refine IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) ?_
    rw [← pow_succ', Nat.sub_add_cancel hq, hpow]
  have h1 : ∀ k, 0 < k → k < q → IsUnit (1 - ζ.1 ^ k) := by
    intro k hk0 hkq
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    subst hn
    have := isUnit_one_sub_pow n hξ φ ζ.2.1 m (by omega)
    rwa [hφ] at this
  have hlt : ∀ a b : ℕ, a < b → b < q → IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
    intro a b hab hb
    have : ζ.1 ^ a - ζ.1 ^ b = ζ.1 ^ a * (1 - ζ.1 ^ (b - a)) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hab.le]
    rw [this]
    exact (hζu.pow a).mul (h1 _ (by omega) (by omega))
  refine ⟨hpow, ?_, ?_, ?_⟩
  · intro a b hab
    have hv : a.val ≠ b.val := fun h => hab (ZMod.val_injective q h)
    rcases lt_or_gt_of_ne hv with h | h
    · exact hlt _ _ h (ZMod.val_lt b)
    · have := (hlt _ _ h (ZMod.val_lt a)).neg
      rwa [neg_sub] at this
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (X_pow_sub_one_eq q hξ)
    simpa [Polynomial.map_prod, eval_prod, hφ] using h
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (cyclotomic_eq q hξ)
    simp only [map_cyclotomic, Polynomial.map_prod, eval_prod] at h
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, h]
    simp [hφ]

end GlobalTheory.CompanionTheory.PrimAlgProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapSurjective
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapBij

section Res

variable {R : Type} [CommRing R] {F : Shv R}

theorem res_smul {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a :=
  map_smul _ _ _

theorem res_res {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  show (F.obj.map k.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (k ≫ g).op).hom a
  rw [op_comp, F.obj.map_comp]
  rfl

end Res

theorem nsmul_eq_up {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (c : ℕ) (t : M) :
    c • t = (ULift.up (c : ZMod q) : ULift.{1} (ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1

theorem coef_eq_zero (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = 0) : a = 0 := by
  have hq : q ∣ a.val := (hg q i).2.1 V ζ a.val (by
    rw [nsmul_eq_up (q := q), ZMod.natCast_zmod_val]
    exact h)
  rw [← ZMod.natCast_zmod_val a]
  exact (ZMod.natCast_eq_zero_iff _ _).2 hq

theorem coef_unique (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a b : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = (ULift.up b : ULift.{1} (ZMod q)) • twGen i ζ) :
    a = b := by
  refine sub_eq_zero.1 (coef_eq_zero hg i ζ _ ?_)
  have e : (ULift.up (a - b) : ULift.{1} (ZMod q)) = ULift.up a - ULift.up b := rfl
  rw [e, sub_smul, h, sub_self]

theorem coef_agree (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) {V V' : Scheme.{0}} (g : V ⟶ U) (g' : V' ⟶ U)
    (c c' : ZMod q)
    (h : Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    (h' : Sec.res g' x = (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res g' (twGen i ζ))
    (v : V) (v' : V') (hv : g v = g' v') : c = c' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v v' hv
  have : Nonempty ↑(pullback g g') := ⟨z⟩
  have e1 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [← res_res, h, res_smul, res_res]
  have e2 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [pullback.condition, ← res_res, h', res_smul, res_res]
  rw [((hR q i U ζ).1 _ (pullback.fst g g' ≫ g)).1] at e1 e2
  exact coef_unique hg i _ c c' (e1.symm.trans e2)

theorem exists_chart (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) (u : U) :
    ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ u ∈ Set.range g ∧
      ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ) := by
  refine (loc_iff_etale_affine_points U
    (fun V g => ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    ?_).1 ?_ u
  · rintro V W g k ⟨c, hc⟩
    exact ⟨c, by rw [← res_res, hc, res_smul, res_res]⟩
  · obtain ⟨S, hS, hc⟩ := (hg q i).1 U ζ x
    refine ⟨S, hS, fun V g hgS => ?_⟩
    obtain ⟨c, hc⟩ := hc V g hgS
    refine ⟨(c : ZMod q), ?_⟩
    rw [hc, nsmul_eq_up (q := q), ((hR q i U ζ).1 V g).1]
    rfl

theorem kap_injective (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) : Function.Injective (kap i ζ) := by
  refine (injective_iff_map_eq_zero (kap i ζ)).2 fun f hf => LocallyConstant.ext fun u => ?_
  let O : U.Opens := ⟨f ⁻¹' {f u}, f.isLocallyConstant.isOpen_fiber _⟩
  have : Nonempty O.toScheme := ⟨⟨u, rfl⟩⟩
  have hO : ∀ v : O.toScheme, f (O.ι v) = f u := fun v => by
    have : O.ι v ∈ Set.range O.ι := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at this
    exact this
  have h := (hK q i U ζ f).1 O.toScheme O.ι (f u) hO
  rw [hf] at h
  have h0 : Sec.res O.ι (0 : Sec (tw q i) U) = 0 := map_zero _
  rw [h0] at h
  exact coef_eq_zero hg i _ _ h.symm

theorem kap_surjective (hR : RepRoot) (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Function.Surjective (kap i ζ) := by
  intro x
  choose V g hA hE hu c hc using exists_chart hR hg i ζ x
  choose y hy using hu
  have hagree : ∀ (u : U) (v : V u), c (g u v) = c u := fun u v =>
    coef_agree hR hg i ζ x (g (g u v)) (g u) _ _ (hc _) (hc u) (y _) v (hy _)
  have hop : ∀ u, IsOpen (Set.range (g u)) := fun u => by
    have := hE u
    exact (g u).isOpenMap.isOpen_range
  let f : LocallyConstant U (ZMod q) := ⟨c, (IsLocallyConstant.iff_exists_open c).2 fun u =>
    ⟨Set.range (g u), hop u, ⟨y u, hy u⟩, by
      rintro _ ⟨v, rfl⟩
      exact hagree u v⟩⟩
  refine ⟨f, ((sec_ext_glue _ _ U).1 _ _ ?_)⟩
  refine (loc_iff_etale_affine_points U (fun V g => Sec.res g (kap i ζ f) = Sec.res g x) ?_).2 fun u => ?_
  · intro V W g k h
    rw [← res_res, h, res_res]
  · refine ⟨V u, g u, hA u, hE u, ⟨y u, hy u⟩, ?_⟩
    have h := (hK q i U ζ f).1 (V u) (g u) (c u) (hagree u)
    rw [h, hc u, ((hR q i U ζ).1 _ (g u)).1]

theorem kapBij : LcCover → RepRoot → KapSpec → KapBij := fun _ hR hK hg q _ i _ ζ =>
  ⟨kap_injective hK hg i ζ, kap_surjective hR hK hg i ζ⟩

end GlobalTheory.CompanionTheory.KapBij
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EtNatProof

def resHom {R : Type} [CommRing R] (G : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec G U →+ Sec G V :=
  (G.obj.map g.op).hom.toAddMonoidHom

theorem res_res {R : Type} [CommRing R] (G : Shv R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec G U) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {G G' : Shv R} (φ : G ⟶ G') {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec G U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom a) h).symm

theorem kap_zero (hKap : KapSpec) (hTw : TwZero) (hGen : InGen) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (ζ ξ : Prim q Γ(U, ⊤)) (f : LocallyConstant U (ZMod q)) : kap 0 ζ f = kap 0 ξ f := by
  refine ((hKap q 0 U ζ f).2.1 _ ?_).symm
  intro V g a hv
  rw [(hKap q 0 U ξ f).1 V g a hv, hTw hGen q V (primRes g ξ) (primRes g ζ)]

def resMor {q : ℕ} {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (P : Probe C q) (P' : Probe C' q)
    (m : Mor P.L P'.L (RingHom.id ℤ)) (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (i : ℤ)
    (hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f)) :
    ResMor (P.res i) (P'.res i) m where
  τ s c := resHom _ (g c)
  nat s {c c'} φ x := by
    change Sec.res (g c') (Sec.res (P.S.map (m.G.map φ)).unop x) = Sec.res (P'.S.map φ).unop (Sec.res (g c) x)
    rw [res_res, res_res, hg φ]
  ι c x := by
    change Sec.res (g c) (Sec.map (resι _ (tw q i)) (kap i (P.ζ (m.G.obj c)) x)) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [res_map, hι]
  dv s c x := by
    change Sec.res (g c) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) x)
    exact res_map _ _ _

theorem etNat : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.TwZero → CrystallineSemistableComparison.E.EtNat := by
  intro hEt hEM hRep hKap hTw hGen q _ C C' _ _ P P' X X' Y Y' u m g hg hτ hy i hi j x
  obtain ⟨a, ha⟩ := (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).1 x
  have hE := (hEt hGen q C P X Y i j x).1 a ha
  have hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f) := by
    intro c f
    rw [(hKap q i _ (P.ζ (m.G.obj c)) f).2.2 _ (g c), hτ c f]
    rcases hi with rfl | hi
    · exact kap_zero hKap hTw hGen q _ _ _
    · rw [hi c]
  let n := resMor P P' m g hg i hι
  have hE' := hEM ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m n j _ _ hE
  have hglob : n.pullC j 0 (Y.glob i j a) = Y'.glob i j (Sec.res u a) := by
    funext t
    change Sec.res (g (t.obj (Fin.last 0))) (Sec.res (Y.y (m.G.obj (t.obj (Fin.last 0)))) a) =
      Sec.res (Y'.y (t.obj (Fin.last 0))) (Sec.res u a)
    rw [res_res, res_res, hy]
  rw [hglob] at hE'
  have hR : Rep (pull _ (sch.map u) _ j x) (Sec.res u a) :=
    (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.2.2.2 X' u x a ha
  exact (hEt hGen q C' P' X' Y' i j _).2 _ ⟨_, hR, hE'⟩

end GlobalTheory.CompanionTheory.EtNatProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterTrivialFiniteCovolumeStatement
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modular_character_trivial_finite_covolume : ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (Γ₁ : Subgroup G₁) [Countable Γ₁] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → ∀ δ : G₁ →* ℝ≥0, Measurable δ → (∀ γ ∈ Γ₁, δ γ = 1) → ∀ u, δ u = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain | exact GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedRootOfRep
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem redRoot_of_rep : CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RedRoot := by
  intro hRoot hOp hConc inOp inRed Q q _ _ hq i X ζ ξ hξ
  have h1 : Rep (rootClass i ζ) (resGen i ζ) := (hRoot Q i X ζ).2
  have h2 : Rep (rootClass i ξ) (resGen i ξ) := (hRoot q i X ξ).2
  have h3 := hOp inOp _ _ _ _ (redMap Q q i) X 0 (rootClass i ζ) _ h1
  rw [inRed Q q hq i X ζ ξ hξ] at h3
  exact (hConc (ZMod q) _ X 0 (resGen i ξ)).2.2 _ _ h3 h2

end GlobalTheory.CompanionTheory.EdgeMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducibleStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_irreducible : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  first | exact @GlobalTheory.CompanionTheory.FinRep.sepIrr | exact GlobalTheory.CompanionTheory.FinRep.sepIrr | (intros; apply GlobalTheory.CompanionTheory.FinRep.sepIrr <;> assumption)
end

