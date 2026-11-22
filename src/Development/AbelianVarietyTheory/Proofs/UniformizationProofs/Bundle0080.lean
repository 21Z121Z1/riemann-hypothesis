import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistConvNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.TwistNonvan

theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (hs _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem exists_constHom {W : Type} [CommRing W] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of W)) (r : Z ⟶ Y)
    (z : Z) : ∃ c : W →+* Z.presheaf.stalk z, ∀ w, gs r z ⊤ (scal p w) = c w :=
  ⟨((Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom).comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom), fun w => gs_eq r z ⊤ trivial _⟩

theorem sum_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (D : DegPre V) (k : ℕ) (α : D.X)
    {W : Type} [CommRing W] [Algebra V W] (a : Multiplicative D.X →* Wˣ)
    (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α)
    (hc : ConvT I (twist a f') (twist (a ^ k)⁻¹ g') h) (h0 : ∀ j, (h α).f j = 0) (e : ℕ)
    (Z : Over (Spec (CommRingCat.of V))) (r : Z ⟶ TA V W ⊗ D.P.A) (hl : Lvl I e Z.hom) (z : Z.left) (J)
    (hJ : Good D.P.L z J) (s : Finset D.X) (hs : ∀ β ∉ s, sval (f' β) r.left z J = 0)
    (c : W →+* Z.left.presheaf.stalk z) (hcw : ∀ w, gs r.left z ⊤ (scal (R := W) (fst (TA V W) D.P.A).left w) = c w) :
    ∑ β ∈ s, c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val * (sval (f' β) r.left z J *
      sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) = 0 := by
  classical
  obtain ⟨p, hp, hsum⟩ := hc α
  obtain ⟨s', hs'⟩ := hsum e
  obtain ⟨h₁, h₂⟩ := hs' Z.left r.left (by rw [Over.w r]; exact hl) z J hJ
  have hT : ∀ β, sval (p β) r.left z J = c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val *
      (sval (f' β) r.left z J * sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) := fun β => by
    have e₁ : a (Multiplicative.ofAdd ((k + 1) • β - k • α)) =
        a (Multiplicative.ofAdd β) * (a ^ k)⁻¹ (Multiplicative.ofAdd (α - β)) := by
      rw [MonoidHom.inv_apply, MonoidHom.pow_apply, ← map_pow, ← map_inv, ← map_mul]
      congr 1
      rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      congr 1
      module
    rw [hp β Z r z J hJ, e₁, Units.val_mul, map_mul]
    unfold twist
    rw [sval_scale _ _ _ z hJ, sval_scale _ _ _ z hJ, hcw, hcw]
    ring
  rw [sval_zero _ h0 _ z hJ] at h₂
  rw [← Finset.sum_congr rfl (fun β _ => hT β)]
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun β _ hβ => by rw [hT β, hs β hβ]; ring),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun β _ hβ => h₁ β hβ)]
  exact h₂.symm

theorem exists_level {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (D : DegPre V)
    {k l m : ℕ} {β ga α : D.X} (f : SecBT D (𝟙_ _) k β) (g : SecBT D (𝟙_ _) l ga) (p : SecBT D (𝟙_ _) m α)
    (hp : IsProdB f g p) (hf : ∃ j, f.f j ≠ 0) (hg : ∃ j, g.f j ≠ 0) :
    ∃ e : ℕ, ¬ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      Lvl (IsLocalRing.maximalIdeal V) e (r ≫ (𝟙_ _ ⊗ D.P.A).hom) → ∀ (z : Z) (J), Good D.P.L z J →
        sval p r z J = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsIntegral (Spec (CommRingCat.of V)))
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsAffine (Spec (CommRingCat.of V)))
  let i : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V i
  have := GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (𝟙_ _)
  obtain ⟨j, hj⟩ := GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ f g p
    (fun y J hJ => ⟨_, hp (𝟙_ _ ⊗ D.P.A) (𝟙 _) y J hJ⟩) hf hg
  by_contra hne
  refine hj (GlobalTheory.sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun r hr => ?_) _ D.P.L
    D.P.isLB _ _ _ p (fun e => by
      by_contra h
      exact hne ⟨e, h⟩) j)
  have e : scal (𝟙_ (Over (Spec (CommRingCat.of V)))).hom r = i r := rfl
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y, rfl⟩ := i.surjective y
  rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.mem_jacobson_bot] at hr
  have := (hr y).map i
  rwa [map_add, map_mul, map_one] at this

end GlobalTheory.UU.TwistNonvan

namespace GlobalTheory.UU
open TwistNonvan

theorem exists_twist_conv_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (g : ∀ α, SecBT D (𝟙_ _) 1 α) (α β₀ : D.X), NullFam (IsLocalRing.maximalIdeal V) f → (∃ j, (f β₀).f j ≠ 0) → (∃ j, (g (α - β₀)).f j ≠ 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (Kbar V) ⟶ TA V W) (a : Multiplicative D.X →* Wˣ), FinExt V W ∧ Function.Injective φ.left.appTop.hom ∧ ∀ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' → PullT (toUnit _) g g' → ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h → ∃ j, (h α).f j ≠ 0 := by
  intro V _ _ _ hV D k f g α β₀ hnull hf hg
  classical
  obtain ⟨hd, hcpl, hch⟩ := hV
  obtain ⟨p, hp⟩ := exists_isProdB V D (𝟙_ _) k 1 β₀ (α - β₀) α (by abel) (f β₀) (g (α - β₀))
  obtain ⟨e, he⟩ := exists_level D _ _ p hp hf hg
  obtain ⟨s₀, hs₀⟩ := hnull e
  obtain ⟨⟨n, hn, hnu⟩, hcyc⟩ := GlobalTheory.exists_finite_extension_primitive_residue V
  let u : D.X → D.X := fun β => (k + 1) • β - k • α
  have hu : Function.Injective u := fun x y hxy => by
    have h₁ : ((k + 1 : ℕ) : ℤ) • x = ((k + 1 : ℕ) : ℤ) • y := by
      rw [natCast_zsmul, natCast_zsmul]; exact sub_left_injective hxy
    exact smul_right_injective D.X (by positivity) h₁
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion D.X n hn ((insert β₀ s₀).image u)
  obtain ⟨W, iW, iL, iA, φ, ζ, hW, hφ, hnW, hζ, hprim⟩ := hcyc n j₀ hn hnu
  by_contra hne
  have H : ∀ a : Multiplicative D.X →* Wˣ, ∃ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α)
      (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' ∧ PullT (toUnit _) g g' ∧
      ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h ∧ ∀ j, (h α).f j = 0 := fun a => by
    by_contra hh
    refine hne ⟨W, iW, iL, iA, φ, a, hW, hφ, fun f' g' h h₁ h₂ h₃ => ?_⟩
    by_contra h₄
    exact hh ⟨f', g', h, h₁, h₂, h₃, fun j => by_contra fun h₅ => h₄ ⟨j, h₅⟩⟩
  obtain ⟨hfin, hfree, hdom, -, -⟩ := hW
  refine he (GlobalTheory.sval_eq_zero_of_faithfullyFlat_base V W (IsLocalRing.maximalIdeal V) e (𝟙_ _ ⊗ D.P.A) _ D.P.L
    D.P.isLB _ _ _ p ?_)
  intro Z r ω hω hl z J hJ
  let Z' : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom)
  let rr : Z' ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r rfl
  let ωω : Z' ⟶ TA V W := Over.homMk ω hω
  let r' : Z' ⟶ TA V W ⊗ D.P.A := lift ωω (rr ≫ snd _ _)
  have e₁ : r' ≫ toUnit _ ▷ D.P.A = rr := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · simp [r']
  have e₂ : r'.left ≫ (toUnit (TA V W) ▷ D.P.A).left = rr.left := congrArg (fun q => q.left) e₁
  have e₃ : r' ≫ snd _ _ = rr ≫ snd _ _ := lift_snd _ _
  obtain ⟨c, hc⟩ := exists_constHom (W := W) (fst (TA V W) D.P.A).left r'.left z
  let T : D.X → Z'.left.presheaf.stalk z := fun β => sval (f β) rr.left z J * sval (g (α - β)) rr.left z J *
      (cubV D.cub (T := Z') z J (toUnit Z' ≫ D.c β) (toUnit Z' ≫ D.c (α - β)) (rr ≫ snd _ D.P.A)).val
  have e₄ : sval p rr.left z J = T β₀ := hp Z' rr z J hJ
  letI : Module W (Z'.left.presheaf.stalk z) := Module.compHom _ c
  have key := hj₀ j₀ le_rfl W ζ hnW hζ hprim (Z'.left.presheaf.stalk z) (Function.extend u T 0) (fun a _ => by
    obtain ⟨f', g', h, h₁, h₂, h₃, h₄⟩ := H a
    have v₁ : ∀ β, sval (f' β) r'.left z J = sval (f β) rr.left z J := fun β =>
      (h₁ β _ r'.left z J hJ).trans (by rw [e₂])
    have v₂ : ∀ β, sval (g' β) r'.left z J = sval (g β) rr.left z J := fun β =>
      (h₂ β _ r'.left z J hJ).trans (by rw [e₂])
    have := sum_eq_zero _ D k α a f' g' h h₃ h₄ e Z' r' hl z J hJ (insert β₀ s₀) (fun β hβ =>
      (v₁ β).trans (hs₀ β (fun hb => hβ (Finset.mem_insert_of_mem hb)) Z r hl z J hJ)) c hc
    rw [Finset.sum_image (fun x _ y _ hxy => hu hxy)]
    refine Eq.trans (Finset.sum_congr rfl fun β _ => ?_) this
    rw [hu.extend_apply, v₁, v₂, e₃]
    rfl) (u β₀) (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
  rw [hu.extend_apply] at key
  exact e₄.trans key

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionLimit

section Alg

variable {R : Type} [CommRing R] (I : Ideal R)

theorem exists_lim [IsPrecomplete I R] (c : ∀ e : ℕ, R ⧸ I ^ (e + 1))
    (hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1)) = c e) :
    ∃ a : R, ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) a = c e := by
  choose x hx using fun e => Ideal.Quotient.mk_surjective (c e)
  have h1 : ∀ e, x e - x (e + 1) ∈ I ^ (e + 1) := fun e => by
    rw [← Ideal.Quotient.eq, hx, ← hc e, ← hx, Ideal.Quotient.factor_mk]
  have h2 : ∀ m n, m ≤ n → x m - x n ∈ I ^ m := fun m n h => by
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := (I ^ m).add_mem ih (Ideal.pow_le_pow_right (hmn.trans (Nat.le_succ n)) (h1 n))
      simpa using this
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance (f := x) (fun {m n} h => by
    rw [SModEq.sub_mem]; simpa using h2 m n h)
  refine ⟨a, fun e => ?_⟩
  have h3 : x (e + 1) - a ∈ I ^ (e + 1) := by
    have := ha (e + 1)
    rw [SModEq.sub_mem] at this
    simpa using this
  rw [← hx, eq_comm, Ideal.Quotient.eq]
  simpa using (I ^ (e + 1)).add_mem (h1 e) h3

theorem eq_of_mk_eq [IsHausdorff I R] {a b : R}
    (h : ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) a = Ideal.Quotient.mk (I ^ (e + 1)) b) : a = b := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) (M := R) inferInstance _ fun n => ?_
  rw [SModEq.zero]
  simpa using Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 (h n))

end Alg

section Calc

variable {X Y Y' : Scheme.{0}} {L : LB X}

theorem exists_pull {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      (∀ j (le : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j),
        s'.f j = (Y'.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨pullSec L φ ε s h, fun _ _ => rfl, fun Z r z J hJ => SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

def linSec {M : LB Y} {N : ℕ} (c : Fin N → Γ(Y, ⊤)) (t : Fin N → LB.Sec M) : LB.Sec M where
  f j := ∑ i, resTop _ (c i) * (t i).f j
  compat i j := by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (SecOps.secScale (c k) (t k)).compat i j

variable {C : Type} [CommRing C] {n N : ℕ}

def Rep (π : Y ⟶ X) (f : Y ⟶ Sp C) (β : Fin N → H0 L n)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (n : ℤ)))) (c : Fin N → C) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
    sval s r z J = ∑ i, cst (r ≫ f) z (c i) * sval (β i) (r ≫ π) z J

theorem rep_transport {π : Y ⟶ X} {f : Y ⟶ Sp C} {β : Fin N → H0 L n} (e : Y' ≅ Y)
    {π' : Y' ⟶ X} {f' : Y' ⟶ Sp C} (hπ : e.hom ≫ π = π') (hf : e.hom ≫ f = f')
    (H : ∀ s, ∃! c, Rep π f β s c) : ∀ s, ∃! c, Rep π' f' β s c := by
  subst hπ hf
  intro s'
  obtain ⟨s, -, hs⟩ := exists_pull s' e.inv (fun _ : Fin 1 => π) (fun _ => e.inv_hom_id_assoc π)
  have key : ∀ c, Rep (e.hom ≫ π) (e.hom ≫ f) β s' c ↔ Rep π f β s c := fun c => by
    constructor
    · intro h Z r z J hJ
      rw [hs Z r z J hJ, h Z _ z J hJ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · intro h Z r z J hJ
      have := h Z (r ≫ e.hom) z J hJ
      rw [hs Z _ z J hJ] at this
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
  simp only [key]
  exact H s

theorem sval_linSec {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (f : Y ⟶ Sp C) (c : Fin N → C)
    (t : Fin N → LB.Sec (LB.LinComb L φ ε)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    sval (linSec (fun i => scal f (c i)) t) r z J = ∑ i, cst (r ≫ f) z (c i) * sval (t i) r z J := by
  rw [SectionScalarValuation.sval_lin (s := linSec (fun i => scal f (c i)) t) (fun i => scal f (c i)) t (fun _ => rfl) r z hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_pull r f z ⊤ trivial _)

end Calc

theorem exists_basis (hS : SecBaseChangeSt) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (N : ℕ) (β : Fin N → H0 P.L n), ∀ (C : Type) [CommRing C] (q : Sp C ⟶ Sp R) (Y : Scheme.{0})
      (π : Y ⟶ P.A.left) (f : Y ⟶ Sp C), IsPullback f π q P.A.hom → ∀ s, ∃! c, Rep π f β s c := by
  have hL := P.isLB
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of R)) P n hn (closedPoint R)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let V := overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤
  let t₀ : Spec (CommRingCat.of R) ⟶ V.left := (Spec (CommRingCat.of R)).topIso.inv
  have ht : t₀ ≫ V.hom = 𝟙 _ := by
    show (Spec (CommRingCat.of R)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.inv_hom_id
  have ht' : V.hom ≫ t₀ = 𝟙 _ := by
    show (Scheme.Opens.ι ⊤ ≫ 𝟙 _) ≫ (Spec (CommRingCat.of R)).topIso.inv = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.hom_inv_id
  let u : P.A ⟶ V := Over.homMk (P.A.hom ≫ t₀) (by rw [Category.assoc, ht, Category.comp_id])
  have hu : snd V P.A ≫ u = fst V P.A := Over.OverMorphism.ext (by
    show (snd V P.A).left ≫ P.A.hom ≫ t₀ = (fst V P.A).left
    rw [← Category.assoc, Over.w (snd V P.A), ← Over.w (fst V P.A), Category.assoc, ht', Category.comp_id])
  have e₁ : lift u (𝟙 P.A) ≫ snd V P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd V P.A ≫ lift u (𝟙 P.A) = 𝟙 _ := by
    rw [comp_lift, hu, Category.comp_id, lift_fst_snd]
  choose β hβ0 hβ using fun i => exists_pull (K := Fin 1) (b i) (lift u (𝟙 P.A)).left (fun _ => 𝟙 P.A.left)
    (fun _ => congrArg CommaMorphism.left e₁)
  refine ⟨_, β, fun C _ q Y π f hp => ?_⟩
  let t : Spec (CommRingCat.of C) ⟶ V.left := q ≫ t₀
  have hq : (baseAt t).hom = q := by
    show (q ≫ t₀) ≫ V.hom = q
    rw [Category.assoc, ht, Category.comp_id]
  choose b' hb0 hb' using fun i => exists_pull (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
  obtain ⟨hli, hsp⟩ := hb C t b' (fun i j => hb0 i j _)
  have e₃ : snd (baseAt t) P.A ≫ lift u (𝟙 P.A) = homAt t ▷ P.A := by
    rw [← whiskerRight_snd (homAt t) P.A, Category.assoc, e₂, Category.comp_id]
  have e₄ : (snd (baseAt t) P.A).left ≫ (lift u (𝟙 P.A)).left = (homAt t ▷ P.A).left :=
    congrArg CommaMorphism.left e₃
  have hp' : IsPullback f π (baseAt t).hom P.A.hom := hq ▸ hp
  refine rep_transport (Y := (baseAt t ⊗ P.A).left) (π := (snd (baseAt t) P.A).left)
    (f := (fst (baseAt t) P.A).left) hp'.isoPullback hp'.isoPullback_hom_snd hp'.isoPullback_hom_fst fun s => ?_
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  have hv : ∀ (c : Fin (n ^ P.g) → C) (Z : Scheme.{0}) (r : Z ⟶ (baseAt t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      sval (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b') r z J =
        ∑ i, cst (r ≫ (fst (baseAt t) P.A).left) z (c i) * sval (β i) (r ≫ (snd (baseAt t) P.A).left) z J :=
    fun c Z r z J hJ => by
      rw [sval_linSec _ _ _ _ _ hJ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb' i Z r z J hJ, hβ i Z _ z J hJ, Category.assoc, e₄]
  have key : ∀ c : Fin (n ^ P.g) → C, Rep (snd (baseAt t) P.A).left (fst (baseAt t) P.A).left β s c ↔
      ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) •
        (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s := fun c => by
    have ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) •
        (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j =
        (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b').f j := fun j => by
      rw [Submodule.coe_sum, Finset.sum_apply]
      rfl
    constructor
    · intro h
      refine Subtype.ext (funext fun j => (ev j).trans ?_)
      exact sec_ext_val hL (fun y J hJ => (hv c _ _ y J hJ).trans (h _ _ y J hJ).symm) j
    · intro h Z r z J hJ
      have : s = linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b' :=
        SecOps.sec_ext fun j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)
      rw [this]
      exact hv c Z r z J hJ
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))
  choose a ha using fun i => bij.2 (r i)
  obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (a i)) = r := funext ha
  refine ⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i

theorem existsUnique_sec_of_compatible : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Geo.Tor.Good P.L z J → Geo.Tor.sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = Geo.Tor.sval (s e) r z J) → ∃! σ : H0 P.L n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Geo.Tor.Good P.L z J → Geo.Tor.sval σ (r ≫ (fstG I e P.A).left) z J = Geo.Tor.sval (s e) r z J := by
  intro hS R _ _ _ I _ P n hn s hs
  have hL := P.isLB
  obtain ⟨N, β, hβ⟩ := exists_basis hS R P n hn
  have hpe : ∀ e, IsPullback (thickObj R I e P.A).hom (fstG I e P.A).left (thick R I e) P.A.hom :=
    fun e => (IsPullback.of_hasPullback P.A.hom (thick R I e)).flip
  choose c hc hcu using fun e => hβ _ _ _ _ _ (hpe e) (s e)
  have hcomp : ∀ e i, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1) i) = c e i :=
    fun e => congrFun (hcu e (fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (c (e + 1) i)) fun Z r z J hJ => by
        have h₁ : thickMap R I e P.A ≫ (thickObj R I (e + 1) P.A).hom =
            (thickObj R I e P.A).hom ≫ thickTrans R I e := pullback.lift_snd _ _ _
        have h₂ : thickMap R I e P.A ≫ (fstG I (e + 1) P.A).left = (fstG I e P.A).left :=
          (pullback.lift_fst _ _ _).trans (Category.comp_id _)
        rw [← hs e Z r z J hJ, hc (e + 1) Z _ z J hJ, Category.assoc, Category.assoc, h₁, h₂, ← Category.assoc]
        exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _))
  choose a ha using fun i => exists_lim I (fun e => c e i) (fun e => hcomp e i)
  have down : ∀ (σ : H0 P.L n) (a : Fin N → R), Rep (𝟙 _) P.A.hom β σ a → ∀ (e : ℕ) (Z : Scheme.{0})
      (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      sval σ (r ≫ (fstG I e P.A).left) z J = ∑ i, cst (r ≫ (thickObj R I e P.A).hom) z
        (Ideal.Quotient.mk (I ^ (e + 1)) (a i)) * sval (β i) (r ≫ (fstG I e P.A).left) z J :=
    fun σ a h e Z r z J hJ => by
      rw [h Z _ z J hJ, Category.comp_id, Category.assoc, ← (hpe e).w, ← Category.assoc]
      exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _)
  have hlin : Rep (𝟙 _) P.A.hom β (linSec (fun i => scal P.A.hom (a i)) β) a := fun Z r z J hJ => by
    rw [sval_linSec _ _ _ _ _ hJ, Category.comp_id]
  refine ⟨linSec (fun i => scal P.A.hom (a i)) β, fun e Z r z J hJ => ?_, fun σ hσ => ?_⟩
  · rw [down _ a hlin e Z r z J hJ, hc e Z r z J hJ]
    simp only [ha]
  · obtain ⟨a', ha', -⟩ := hβ R (𝟙 _) _ (𝟙 _) P.A.hom (IsPullback.of_vert_isIso ⟨by simp⟩) σ
    have : a' = a := funext fun i => eq_of_mk_eq I fun e => by
      rw [ha]
      exact congrFun (hcu e (fun i => Ideal.Quotient.mk (I ^ (e + 1)) (a' i)) fun Z r z J hJ =>
        (hσ e Z r z J hJ).symm.trans (down σ a' ha' e Z r z J hJ)) i
    subst this
    exact SecOps.sec_ext (sec_ext_val hL fun y J hJ => (ha' _ _ y J hJ).trans (hlin _ _ y J hJ).symm)

end GlobalTheory.SectionLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory

namespace PsiScalIn

open PsiInPull PsiInPow

variable {R : Type} [CommRing R] [IsDomain R]

def sig (z : Spec (CommRingCat.of (FractionRing R))) :
    FractionRing R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z :=
  ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

theorem gs_scal_id (z : Spec (CommRingCat.of (FractionRing R))) (c : FractionRing R) :
    gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing R)))) c) = sig z c := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem gs_toOpen (z : Spec (CommRingCat.of (FractionRing R))) (V : (Spec (CommRingCat.of R)).Opens)
    (hz : jK R z ∈ V) (r : R) : gs (jK R) z V (DegPre.toOpen V r) = sig z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  refine (gs_res (jK R) z (le_top : V ≤ ⊤) hz _).trans ((gs_eq (jK R) z ⊤ trivial _).trans ?_)
  simp only [sig, RingHom.comp_apply]
  rw [nat]
  rfl

theorem key (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (q : D.P.L.ι)
    (V : (Spec (CommRingCat.of R)).Opens) (hle : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q)
    (z : Spec (CommRingCat.of (FractionRing R))) (hz : jK R z ∈ V) :
    ∃ u : Γ(Spec (CommRingCat.of R), V)ˣ,
      (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val =
        sig z (a χ).val * gs (jK R) z V u.val := by
  have hle' : V ≤ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => q) := fun y hy =>
    mem_wchart _ _ _ _ (hle hy)
  obtain ⟨J, hJ, e⟩ := exists_good D.P.L D.P.isLB (Z := (TK R).left) z (K := PUnit) (fun _ => D.xK χ) (fun _ => q)
    (fun _ _ _ => rfl) (fun _ => hle hz)
  have e0 : J (D.xK χ) = q := e PUnit.unit
  have v := (h χ).2 (TK R) (𝟙 _) z J hJ
  have v1 := val_of (D.psi χ) (𝟙 _) z J (fun _ => q) (fun _ => (congrArg J (Category.id_comp _)).trans e0)
  have v2 := val_of (ga χ) (toUnit (TK R)).left z J (fun _ => q) (fun _ => e0)
  refine ⟨res hle' ((ga χ).s (fun _ => q)), (congrArg Units.val v1).symm.trans (v.trans ?_)⟩
  refine congrArg₂ (· * ·) (gs_scal_id z _) ?_
  refine (congrArg Units.val v2).trans ?_
  exact ((gs_unit _ _ _ hz _).trans (congrArg Units.val (gm_res _ _ hle' hz _))).symm

theorem main_local [IsLocalRing R] (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (J : Ideal R) :
    D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap R (FractionRing R) r = (a χ).val := by
  constructor
  · intro H
    obtain ⟨q, hq⟩ := exists_chart D.P.isLB ((D.c χ).left (IsLocalRing.closedPoint R))
    have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q := fun y _ =>
      (IsLocalRing.specializes_closedPoint y).mem_open ((D.c χ).left ⁻¹ᵁ D.P.L.U q).isOpen hq
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
    obtain ⟨r, hr, e⟩ := gs_of_psiIn D χ J H q ⊤ (isAffineOpen_top _) hle z trivial
    obtain ⟨u, hu⟩ := key D ga a h χ q ⊤ hle z trivial
    have hs : Function.Surjective (DegPre.toOpen (R := R) ⊤) := by
      intro b
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b, ?_⟩
      simp [DegPre.toOpen]
    obtain ⟨s, hsJ, es⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 (Ideal.mul_mem_right (u⁻¹).val _ hr)
    refine ⟨s, hsJ, (sig z).injective ?_⟩
    have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
    rw [← gs_toOpen z ⊤ hz, es, gs_mul _ _ _ hz, e.trans hu, _root_.mul_assoc,
      ← gs_mul _ _ _ hz, Units.mul_inv, gs_eq _ _ _ hz, map_one, map_one, _root_.mul_one]
  · rintro ⟨r, hr, e⟩
    refine psiIn_of_gs D χ J fun q V _ hle z hz => ?_
    obtain ⟨u, hu⟩ := key D ga a h χ q V hle z hz
    refine ⟨DegPre.toOpen V r * u.val, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr), ?_⟩
    rw [gs_mul _ _ _ hz, gs_toOpen z V hz, e]
    exact hu.symm

end PsiScalIn

theorem psiIn_iff_scalar_mem : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → ∀ (χ : D.X) (J : Ideal V), J ≠ ⊥ → (D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap V (FractionRing V) r = (a χ).val) :=
  fun _ _ _ _ D ga a h χ J _ => PsiScalIn.main_local D ga a h χ J

end GlobalTheory
end
end

