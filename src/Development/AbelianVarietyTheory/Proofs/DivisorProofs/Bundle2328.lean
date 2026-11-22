import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
open scoped TensorProduct

namespace GlobalTheory.GenericFibreInt

theorem exists_nat_mul_mem (F : Type) [Field F] [NumberField F] (c : F) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ o : 𝓞 F, (N : F) * c = algebraMap (𝓞 F) F o := by
  obtain ⟨y, hy, hi⟩ :=
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  let o : 𝓞 F := ⟨y • c, hi⟩
  have key : algebraMap (𝓞 F) F o = (y : F) * c := by
    simp [o, zsmul_eq_mul]
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · refine ⟨o, ?_⟩
    have h' : ((y.natAbs : ℤ) : F) = (y : F) := by rw [← h]
    rw [key, ← h', Int.cast_natCast]
  · refine ⟨-o, ?_⟩
    have h' : ((y.natAbs : ℤ) : F) = -(y : F) := by
      rw [← Int.cast_neg]; congr 1; omega
    rw [map_neg, key, ← Int.cast_natCast, h', neg_mul]

theorem tensor_int (F A : Type) [Field F] [NumberField F] [CommRing A] [Algebra (𝓞 F) A]
    (t : A ⊗[𝓞 F] F) : ∃ N : ℕ, N ≠ 0 ∧ ∃ a : A, N • t = a ⊗ₜ[𝓞 F] (1 : F) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul a c =>
    obtain ⟨N, hN, o, ho⟩ := exists_nat_mul_mem F c
    refine ⟨N, hN, o • a, ?_⟩
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul, ho, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨N₁, hN₁, a₁, e₁⟩ := h₁
    obtain ⟨N₂, hN₂, a₂, e₂⟩ := h₂
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, N₂ • a₁ + N₁ • a₂, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm N₁ N₂ t₁, e₁, e₂, TensorProduct.add_tmul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul']

theorem resG_resG' {Y : Scheme.{0}} {A B C : Y.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B) (z : Γ(Y, A)) :
    resG Y h₂ (resG Y h₁ z) = resG Y (h₂.trans h₁) z := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_self' {Y : Scheme.{0}} {A : Y.Opens} (h : A ≤ A) (z : Γ(Y, A)) : resG Y h z = z := by
  simp only [resG]
  rw [show homOfLE h = 𝟙 A from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem app_resG' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U V : Z.Opens} (h : V ≤ U) (a : Γ(Z, U)) :
    (φ.app V).hom (resG Z h a) = resG Y (φ.preimage_mono h) ((φ.app U).hom a) := by
  change ((Z.presheaf.map (homOfLE h).op ≫ φ.app V).hom) a = _
  rw [Scheme.Hom.naturality]
  rfl

variable {F : Type} [Field F] [NumberField F] {X G : Scheme.{0}} {p : X ⟶ Sp (𝓞 F)} {q : G ⟶ Sp F}
  {j : G ⟶ X}

theorem integ (H : IsPullback j q p (spMap (algebraMap (𝓞 F) F))) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(G, j ⁻¹ᵁ U)) : ∃ N : ℕ, N ≠ 0 ∧ ∃ a : Γ(X, U), (N : Γ(G, j ⁻¹ᵁ U)) * s = (j.app U).hom a := by
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  have hle : j ⁻¹ᵁ U ⊓ q ⁻¹ᵁ ⊤ ≤ j ⁻¹ᵁ U := inf_le_left
  have hge : j ⁻¹ᵁ U ≤ j ⁻¹ᵁ U ⊓ q ⁻¹ᵁ ⊤ := le_inf le_rfl le_top
  obtain ⟨N, hN, a, ha⟩ :=
    tensor_int F Γ(X, U) ((ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p q j H U hU).symm (resG G hle s))
  refine ⟨N, hN, a, ?_⟩
  have e := congrArg (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p q j H U hU) ha
  rw [map_nsmul, RingEquiv.apply_symm_apply, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul, map_one, mul_one,
    nsmul_eq_mul] at e
  have e2 := congrArg (resG G hge) e
  rw [map_mul, map_natCast, resG_resG', resG_self'] at e2
  rw [e2]
  show ((j.appLE U _ inf_le_left ≫ G.presheaf.map (homOfLE hge).op).hom a) = _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE]

theorem eq_mul_inverse_pow {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (h : Γ(Y, U)) (V : Y.Opens)
    (E : V = Y.basicOpen h) (z : Γ(Y, V)) :
    ∃ (n : ℕ) (b : Γ(Y, U)), z * resG Y (E.le.trans (Y.basicOpen_le h)) h ^ n =
      resG Y (E.le.trans (Y.basicOpen_le h)) b := by
  subst E
  haveI := hU.isLocalization_basicOpen h
  obtain ⟨⟨b, _, n, rfl⟩, hb⟩ := IsLocalization.surj (Submonoid.powers h) z
  exact ⟨n, b, by rw [← map_pow]; exact hb⟩

end GlobalTheory.GenericFibreInt

namespace GlobalTheory.GenericFibreInt

theorem exists_nat_mul_eq_app : ∀ (F : Type) [Field F] [NumberField F] (X G : Scheme.{0}) (p : X ⟶ Sp (𝓞 F))
    (q : G ⟶ Sp F) (j : G ⟶ X), IsPullback j q p (spMap (algebraMap (𝓞 F) F)) →
    ∀ (W : G.Opens) (x : G), x ∈ W → ∀ (ι : Type) [Fintype ι] (g : ι → Γ(G, W)),
      ∃ (W' : X.Opens) (h : j ⁻¹ᵁ W' ≤ W), x ∈ j ⁻¹ᵁ W' ∧ ∃ (n : ℕ) (g' : ι → Γ(X, W')), n ≠ 0 ∧
        ∀ a, (n : Γ(G, j ⁻¹ᵁ W')) * resG G h (g a) = j.app W' (g' a) := by
  intro F _ _ X G p q j H W x hx ι _ g
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hjx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (j x)) isOpen_univ
  have hU' : IsAffineOpen (j ⁻¹ᵁ U) := TopForm.isAffineOpen_preimage_of_isPullback H hU
  obtain ⟨h, hle, hxh⟩ := hU'.exists_basicOpen_le (V := W ⊓ j ⁻¹ᵁ U) ⟨x, hx, hjx⟩ hjx
  obtain ⟨N₀, hN₀, h', hh'⟩ := integ H hU h
  have hunit : IsUnit (N₀ : Γ(G, j ⁻¹ᵁ U)) := by
    have : IsUnit (N₀ : F) := (Nat.cast_ne_zero.2 hN₀).isUnit
    simpa using this.map (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q (j ⁻¹ᵁ U))
  have E : j ⁻¹ᵁ X.basicOpen h' = G.basicOpen h := by
    rw [Scheme.preimage_basicOpen, ← hh', Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit G hunit]
    exact inf_eq_right.2 (G.basicOpen_le h)
  have hVU : j ⁻¹ᵁ X.basicOpen h' ≤ j ⁻¹ᵁ U := E.le.trans (G.basicOpen_le h)
  have hVW : j ⁻¹ᵁ X.basicOpen h' ≤ W := E.le.trans (hle.trans inf_le_left)
  have key : ∀ a, ∃ N : ℕ, N ≠ 0 ∧ ∃ c : Γ(X, X.basicOpen h'),
      (N : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVW (g a) = (j.app (X.basicOpen h')).hom c := by
    intro a
    obtain ⟨n, b, hb⟩ := eq_mul_inverse_pow hU' h _ E (resG G hVW (g a))
    obtain ⟨N, hN, b', hb'⟩ := integ H hU b
    obtain ⟨u, hu⟩ : IsUnit (resG X (X.basicOpen_le h') h') := X.toRingedSpace.isUnit_res_basicOpen h'
    refine ⟨N, hN, resG X (X.basicOpen_le h') ((N₀ : Γ(X, U)) ^ n * b') * ((u⁻¹ : _ˣ) : Γ(X, _)) ^ n, ?_⟩
    have f1 : (j.app (X.basicOpen h')).hom (resG X (X.basicOpen_le h') ((N₀ : Γ(X, U)) ^ n * b')) =
        (N₀ : Γ(G, j ⁻¹ᵁ X.basicOpen h')) ^ n * N * resG G hVU b := by
      rw [app_resG', map_mul, map_pow, map_natCast, ← hb', map_mul, map_mul, map_pow, map_natCast, map_natCast,
        mul_assoc]
    have f2 : (j.app (X.basicOpen h')).hom (u : Γ(X, _)) = (N₀ : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVU h := by
      rw [hu, app_resG', ← hh', map_mul, map_natCast]
    have hJu : (j.app (X.basicOpen h')).hom (u : Γ(X, _)) * (j.app (X.basicOpen h')).hom ((u⁻¹ : _ˣ) : Γ(X, _)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have one : (N₀ : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVU h *
        (j.app (X.basicOpen h')).hom ((u⁻¹ : _ˣ) : Γ(X, _)) = 1 := by rw [← f2, hJu]
    rw [map_mul, map_pow, f1, ← hb]
    calc (N : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVW (g a)
        = (N : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVW (g a) * ((N₀ : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVU h *
          (j.app (X.basicOpen h')).hom ((u⁻¹ : _ˣ) : Γ(X, _))) ^ n := by rw [one, one_pow, mul_one]
      _ = _ := by ring
  choose Nf hNf c hc using key
  refine ⟨X.basicOpen h', hVW, E ▸ hxh, ∏ a, Nf a, fun a => ((∏ a' ∈ Finset.univ.erase a, Nf a' : ℕ) : Γ(X, _)) * c a,
    Finset.prod_ne_zero_iff.2 fun a _ => hNf a, fun a => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a), Nat.cast_mul, mul_assoc, hc a]
  show _ = (j.app (X.basicOpen h')).hom _
  rw [map_mul, map_natCast]

end GlobalTheory.GenericFibreInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantLocalEquationCartierFiniteQuotien
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvEqn

variable {X : Scheme.{0}} [IsIntegral X]

theorem regAt_map (φ : X ⟶ X) [IsDominant φ] {x : X} {f : X.functionField} (h : RegAt (φ x) f) :
    RegAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨φ.stalkMap x a, (GlobalTheory.functionFieldMap_algebraMap φ x a).symm⟩

theorem zeroAt_map (φ : X ⟶ X) [IsDominant φ] {x : X} {f : X.functionField} (h : ZeroAt (φ x) f) :
    ZeroAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨φ.stalkMap x a, map_nonunit (φ.stalkMap x).hom a ha,
    (GlobalTheory.functionFieldMap_algebraMap φ x a).symm⟩

theorem map_genericPoint (φ : X ⟶ X) [IsDominant φ] : φ (genericPoint X) = genericPoint X := by
  have := (genericPoint_spec X).image φ.continuous
  rw [Set.image_univ, φ.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec X)

theorem functionFieldMap_comp (φ ψ : X ⟶ X) [IsDominant φ] [IsDominant ψ] [IsDominant (φ ≫ ψ)]
    (f : X.functionField) :
    GlobalTheory.functionFieldMap (φ ≫ ψ) f = GlobalTheory.functionFieldMap φ (GlobalTheory.functionFieldMap ψ f) := by
  have hz : (φ ≫ ψ) (genericPoint X) = genericPoint X := map_genericPoint _
  have hr : RegAt (ψ (φ (genericPoint X))) f := by
    rw [show ψ (φ (genericPoint X)) = (φ ≫ ψ) (genericPoint X) from rfl, hz]
    exact regAt_genericPoint f
  obtain ⟨a, rfl⟩ := hr
  rw [GlobalTheory.functionFieldMap_algebraMap ψ, GlobalTheory.functionFieldMap_algebraMap φ]
  have := GlobalTheory.functionFieldMap_algebraMap (φ ≫ ψ) (genericPoint X) a
  refine this.trans ?_
  rw [Scheme.Hom.stalkMap_comp]
  rfl

theorem UnitAt.add_zeroAt {x : X} {f f' : X.functionField} (h : UnitAt x f) (h' : ZeroAt x f') :
    UnitAt x (f + f') := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  refine ⟨a + b, ?_, map_add _ a b⟩
  by_contra hu
  have h1 : a + b ∈ IsLocalRing.maximalIdeal _ := hu
  exact ((IsLocalRing.mem_maximalIdeal _).1 (by simpa using sub_mem h1 hb)) ha

variable {Γ : Type} [Group Γ]

def sig (ρ : Γ →* Aut X) (γ : Γ) : X.functionField →+* X.functionField :=
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  GlobalTheory.functionFieldMap (ρ γ).hom

theorem fnAct_val (ρ : Γ →* Aut X) (γ : Γ) (g : X.functionFieldˣ) :
    ((fnAct ρ γ g : X.functionFieldˣ) : X.functionField) = sig ρ γ g := rfl

theorem regAt_sig (ρ : Γ →* Aut X) (γ : Γ) {x : X} {f : X.functionField}
    (h : RegAt ((ρ γ).hom x) f) : RegAt x (sig ρ γ f) :=
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  regAt_map _ h

theorem zeroAt_sig (ρ : Γ →* Aut X) (γ : Γ) {x : X} {f : X.functionField}
    (h : ZeroAt ((ρ γ).hom x) f) : ZeroAt x (sig ρ γ f) :=
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  zeroAt_map _ h

theorem sig_sig (ρ : Γ →* Aut X) (γ δ : Γ) (f : X.functionField) :
    sig ρ γ (sig ρ δ f) = sig ρ (δ * γ) f := by
  haveI : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  haveI : IsIso (ρ δ).hom := Iso.isIso_hom (ρ δ)
  haveI : IsIso (ρ (δ * γ)).hom := Iso.isIso_hom (ρ (δ * γ))
  have e : (ρ (δ * γ)).hom = (ρ γ).hom ≫ (ρ δ).hom := by rw [map_mul]; rfl
  have key : ∀ (φ : X ⟶ X) (h : φ = (ρ γ).hom ≫ (ρ δ).hom) [IsDominant φ],
      GlobalTheory.functionFieldMap φ f = GlobalTheory.functionFieldMap (ρ γ).hom (GlobalTheory.functionFieldMap (ρ δ).hom f) := by
    intro φ h _
    subst h
    exact functionFieldMap_comp _ _ f
  exact (key _ e).symm

theorem sig_one (ρ : Γ →* Aut X) (f : X.functionField) : sig ρ 1 f = f := by
  have := sig_sig ρ 1 1 f
  rw [mul_one] at this
  exact (sig ρ 1).injective this

theorem eq_of_mem_closure [Finite Γ] (ρ : Γ →* Aut X) (γ : Γ) (x : X)
    (h : x ∈ closure ({(ρ γ).hom x} : Set X)) : (ρ γ).hom x = x := by
  set a : ℕ → X := fun k => (ρ (γ ^ k)).hom x with ha
  have hs : ∀ k, a (k + 1) = (ρ γ).hom (a k) := fun k => by
    simp only [ha, pow_succ', map_mul]; rfl
  have h0 : a 0 = x := by simp only [ha, pow_zero, map_one]; rfl
  have h1 : a 1 ⤳ a 0 := by
    rw [h0, hs, h0, specializes_iff_mem_closure]; exact h
  have hstep : ∀ k, a (k + 1) ⤳ a k := fun k => by
    induction k with
    | zero => exact h1
    | succ k ih =>
      have e := ih.map (ρ γ).hom.continuous
      rw [← hs, ← hs] at e
      exact e
  have hge : ∀ k, a (k + 1) ⤳ a 1 := fun k => by
    induction k with
    | zero => exact specializes_rfl
    | succ k ih => exact (hstep (k + 1)).trans ih
  have hn : 0 < orderOf γ := orderOf_pos γ
  have hx : a (orderOf γ) = x := by simp only [ha, pow_orderOf_eq_one, map_one]; rfl
  obtain ⟨m, hm⟩ : ∃ m, orderOf γ = m + 1 := ⟨orderOf γ - 1, by omega⟩
  have e1 : x ⤳ a 1 := by rw [← hx, hm]; exact hge m
  have e2 : a 1 ⤳ x := h0 ▸ h1
  have : a 1 = x := (e2.antisymm e1).eq
  calc (ρ γ).hom x = a 1 := by rw [hs 0, h0]
    _ = x := this

theorem exists_invariant_isEqn : ∀ (F : Type) [Field F] [CharZero F] (X W : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp F)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W), IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ γ x g, D.IsEqn ((ρ γ).hom x) g → D.IsEqn x (fnAct ρ γ g)) →
    (∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)) →
    ∀ x : X, ∃ g : X.functionFieldˣ, (∀ γ, fnAct ρ γ g = g) ∧ D.IsEqn x g := by
  intro F _ _ X W _ s Γ _ _ ρ q hq D hinv hin x
  classical
  haveI := Fintype.ofFinite Γ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q x)) isOpen_univ
  have := hq.isAffineHom
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hxU : x ∈ q ⁻¹ᵁ V := hxV
  have horb (γ : Γ) : (ρ γ).hom x ∈ q ⁻¹ᵁ V := by
    have e : q ((ρ γ).hom x) = q x := congr($(hq.comp_eq γ) x)
    show q _ ∈ V
    rw [e]; exact hxV
  let T : Finset X := Finset.univ.image fun γ : Γ => (ρ γ).hom x
  have hT (y : X) : y ∈ T ↔ ∃ γ, (ρ γ).hom x = y := by simp [T]
  obtain ⟨e₀, he₀, hv⟩ := GlobalTheory.T.exists_cartierSection_generatesAt_vanishesAt_finset X (q ⁻¹ᵁ V) hU D x hxU T
    (fun y hy => by obtain ⟨γ, rfl⟩ := (hT y).1 hy; exact horb γ)
    (fun y hy hne hc => by
      obtain ⟨γ, rfl⟩ := (hT y).1 hy
      exact hne (eq_of_mem_closure ρ γ x hc))
  have he0 : e₀ ≠ 0 := he₀.ne_zero
  set g : X.functionFieldˣ := (Units.mk0 e₀ he0)⁻¹ with hgdef
  have hgv : (g : X.functionField) = e₀⁻¹ := by simp [hgdef]
  have hg : D.IsEqn x g := CartierDiv.isEqn_iff_generatesAt_inv.2 (by rw [hgv, inv_inv]; exact he₀)

  have hgs (γ : Γ) (hγ : (ρ γ).hom x = x) : D.IsEqn x (fnAct ρ γ g) :=
    hinv γ x g (by rw [hγ]; exact hg)
  let ι := {γ : Γ // (ρ γ).hom x = x}
  let σ : ι → X.functionField →+* X.functionField := fun i => sig ρ i.1
  let u : ι → X.functionField := fun i => (g : X.functionField) / sig ρ i.1 g
  have hu (i : ι) : UnitAt x (u i) := by
    have := (hg.iff_unitAt.1 (hgs i.1 i.2)).inv
    rw [fnAct_val, inv_div] at this
    exact this
  have hnat (n : ℕ) (hn : n ≠ 0) : UnitAt x (n : X.functionField) := by
    let φF := (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ s.appTop ≫ X.presheaf.germ ⊤ x trivial
    refine ⟨(n : X.presheaf.stalk x), ?_, map_natCast _ n⟩
    rw [← map_natCast φF.hom n]
    exact (IsUnit.mk0 (n : F) (Nat.cast_ne_zero.2 hn)).map _
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_affineFunction_weighted_translates_unitAt X (q ⁻¹ᵁ V) hU x hxU ι σ u
    (fun i f hf => regAt_sig ρ i.1 (by rw [i.2]; exact hf))
    (fun i f hf => zeroAt_sig ρ i.1 (by rw [i.2]; exact hf))
    (fun i => (hu i).regAt)
    (fun i hi => by
      have hfr := fromSpecResidueField_comp_eq_of_fixes X Γ ρ i.1 x i.2
        (fun v hv => by rw [fnAct_val]; exact hi v hv)
      have h1 := hin i.1 x g hfr hg
      rw [Units.val_mul, fnAct_val, Units.val_inv_eq_inv_val g] at h1
      have hs0 : sig ρ i.1 g ≠ 0 := by rw [← fnAct_val]; exact Units.ne_zero _
      have hg0 : (g : X.functionField) ≠ 0 := Units.ne_zero _
      have e : u i - 1 = (sig ρ i.1 g * (g : X.functionField)⁻¹ - 1) * ((-1) * u i) := by
        simp only [u]; field_simp; ring
      rw [e]
      exact h1.mul (RegAt.mul (⟨-1, by rw [map_neg, map_one]⟩ : RegAt x (-1)) (hu i).regAt))
    hnat
    ⟨⟨1, by rw [map_one]; rfl⟩, fun f _ => by
      simp only [σ, sig_one, sub_self]; exact zeroAt_zero x⟩
  set af := fnOf (q ⁻¹ᵁ V) (gen_mem hxU) a with haf
  set h : X.functionField := ∑ γ : Γ, sig ρ γ (af * e₀) with hh

  have hinvh (δ : Γ) : sig ρ δ h = h := by
    rw [hh, map_sum]
    simp only [sig_sig]
    exact Equiv.sum_comp (Equiv.mulRight δ) (fun γ => sig ρ γ (af * e₀))

  have hsplit : h * g = ∑ i : ι, σ i af * u i +
      ∑ γ ∈ Finset.univ.filter (fun γ : Γ => ¬ (ρ γ).hom x = x), sig ρ γ (af * e₀) * g := by
    rw [hh, Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun γ : Γ => (ρ γ).hom x = x)]
    congr 1
    rw [Finset.sum_subtype (p := fun γ : Γ => (ρ γ).hom x = x) _ (fun γ => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs0 : sig ρ i.1 g ≠ 0 := by rw [← fnAct_val]; exact Units.ne_zero _
    simp only [σ, u, map_mul, hgv, map_inv₀]
    rw [← hgv]
    field_simp
  have hrest : ZeroAt x (∑ γ ∈ Finset.univ.filter (fun γ : Γ => ¬ (ρ γ).hom x = x),
      sig ρ γ (af * e₀) * g) := by
    refine Finset.sum_induction _ (ZeroAt x) (fun _ _ h h' => h.add h') (zeroAt_zero x)
      fun γ hγ => ?_
    have hne : (ρ γ).hom x ≠ x := (Finset.mem_filter.1 hγ).2
    obtain ⟨g', hg', hz⟩ := hv _ ((hT _).2 ⟨γ, rfl⟩) hne
    have hz' : ZeroAt ((ρ γ).hom x) (af * e₀ * g') := by
      have e : af * e₀ * g' = e₀ * g' * af := by ring
      rw [e]
      exact hz.mul (regAt_fnOf (horb γ) _ a)
    have h2 := zeroAt_sig ρ γ hz'
    have h3 : UnitAt x ((g : X.functionField) / fnAct ρ γ g') :=
      (hinv γ x g' hg').iff_unitAt.1 hg
    rw [fnAct_val] at h3
    have hs0 : sig ρ γ g' ≠ 0 := by rw [← fnAct_val]; exact Units.ne_zero _
    have e : sig ρ γ (af * e₀) * g = sig ρ γ (af * e₀ * g') * ((g : X.functionField) / sig ρ γ g') := by
      rw [map_mul (sig ρ γ) (af * e₀)]; field_simp
    rw [e]
    exact h2.mul h3.regAt
  have hunit : UnitAt x (h * g) := by
    rw [hsplit]; exact UnitAt.add_zeroAt ha hrest
  have hh0 : h ≠ 0 := fun e => by
    have := hunit.ne_zero; rw [e, zero_mul] at this; exact this rfl
  refine ⟨(Units.mk0 h hh0)⁻¹, fun δ => ?_, ?_⟩
  · rw [map_inv]
    congr 1
    ext
    rw [fnAct_val, Units.val_mk0, hinvh]
  · rw [CartierDiv.isEqn_iff_generatesAt_inv, Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0]
    exact hg.generatesAt_iff.2 hunit

end GlobalTheory.InvEqn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerMatrixFirstOrderDeformationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencerMatrix_firstOrderDeformation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hP : GlobalTheory.Published.AbelianDeRham) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (x' : Sp (DualNumber S) ⟶ Xo.X) (h1 : x' ≫ Xo.s = sOf c (DualNumber S))
    (h2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x' = y.x), ∃ Mx : HIx Dw (psiSet H) → S, ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K) (y' : FrPt Xo c K),
      FrMap ψ y y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ x') (ψ ∘ Mx) := by
  first | exact @GlobalTheory.KSFam.ksFamily | exact GlobalTheory.KSFam.ksFamily | (intros; apply GlobalTheory.KSFam.ksFamily <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeTransportersAllComponents
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transp_all : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k, ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k : (uAt r v i).Comp), ∃ (k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v
  obtain ⟨ψ, h1⟩ := GlobalTheory.T.exists_transporter_moves_frame_reads_inverse p hp r h hr i v
  refine ⟨ψ, fun γ k => ?_⟩
  let V := Frame ((uAt r v i).X k).Ψ D.R.r
  let Dk : Set V := ((uAt r v i).X k).dom
  have hDo : IsOpen Dk := FourierCoefficientDomain.isOpen_dom _
  have hDn : Dk.Nonempty := (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).nonempty
  let ι := Σ k' : (uAt r v i).Comp, {a : GL (Fin D.R.r) D.host.E //
    ∃ hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a, ReadsInv p r i v ψ γ k k' a}
  let S : ι → Set V := fun c => {x | ∃ hx : x ∈ Dk, MovesAt p r i v γ k c.1 c.2.1 c.2.2.1 x hx}
  haveI : Countable ι := inferInstance
  obtain ⟨x₀, hx₀⟩ := hDn
  haveI : Nonempty ι := by
    obtain ⟨k', a, hm, hR, -⟩ := h1 γ k x₀ hx₀
    exact ⟨⟨k', a, hm, hR⟩⟩
  haveI : Nonempty Dk := ⟨⟨x₀, hx₀⟩⟩
  haveI : LocallyCompactSpace Dk := hDo.locallyCompactSpace
  let T : ι → Set Dk := fun c => Subtype.val ⁻¹' closure (S c)
  have hTc : ∀ c, IsClosed (T c) := fun c => isClosed_closure.preimage continuous_subtype_val
  have hTu : ⋃ c, T c = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨k', a, hm, hR, hM⟩ := h1 γ k y.1 y.2
    exact Set.mem_iUnion.2 ⟨⟨k', a, hm, hR⟩, subset_closure ⟨y.2, hM⟩⟩
  obtain ⟨c, hc⟩ := nonempty_interior_of_iUnion_of_closed hTc hTu
  obtain ⟨k', a, hm, hR⟩ := c
  refine ⟨k', a, isTransp_of_movesAt hm ?_ hR⟩
  refine GlobalTheory.T.transporter_moves_all_frames_of_dense_open p hp r h hr i v γ k k' a hm (Subtype.val '' interior (T ⟨k', a, hm, hR⟩))
    (hDo.isOpenMap_subtype_val _ isOpen_interior) (hc.image _) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ T ⟨k', a, hm, hR⟩ := interior_subset hy
    exact hy'

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftMonoOfFpqcCoverLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem exists_lift_of_fpqc_cover : ∀ (G T T' Y : Scheme.{0}) (π : G ⟶ Y) [Mono π] (y : T ⟶ Y) (t : T' ⟶ T)
    [Flat t] [Surjective t] [QuasiCompact t] (z : T' ⟶ G), z ≫ π = t ≫ y → ∃ w : T ⟶ G, w ≫ π = y := by
  intro G T T' Y π _ y t _ _ _ z hz
  let s := pullback.snd π y
  let σ : T' ⟶ pullback s t :=
    pullback.lift (pullback.lift z t hz) (𝟙 T') (by rw [Category.id_comp]; exact pullback.lift_snd _ _ _)
  have hσ : σ ≫ pullback.snd s t = 𝟙 T' := pullback.lift_snd _ _ _
  haveI : IsSplitEpi (pullback.snd s t) := ⟨⟨⟨σ, hσ⟩⟩⟩
  haveI : IsIso (pullback.snd s t) := isIso_of_mono_of_isSplitEpi _
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) t :=
    ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
  have hs : IsIso s :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hq (MorphismProperty.isomorphisms.infer_property _)
  refine ⟨inv s ≫ pullback.fst π y, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end GlobalTheory.DualOpen
end

