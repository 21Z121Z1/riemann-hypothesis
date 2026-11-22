import Mathlib
import ReciprocityTheory.DualLattices.Bundle0005
import ReciprocityTheory.DualLattices.Bundle0016
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import ReciprocityTheory.DualLattices.Bundle0006
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
import ReciprocityTheory.DualLattices.Bundle0013

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CompMemAddFun
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
lemma comp_mem_addFun (p : ℕ) (e : X ≃+ Y) {f : Y → C} (hf : f ∈ addFun R p Y) :
    (fun x => f (e x)) ∈ addFun R p X := by
  have h : ∀ a b : Y, f (a + b) - f a - f b ∈ pInt R p := hf
  show ∀ a b : X, f (e (a + b)) - f (e a) - f (e b) ∈ pInt R p
  intro a b
  rw [map_add]
  exact h (e a) (e b)

private theorem map_pbE_eq_of_addEquiv (e : X ≃+ Y) (SX : Submodule R (X → C)) (SY : Submodule R (Y → C))
    (h1 : ∀ f ∈ SY, (fun x => f (e x)) ∈ SX) (h2 : ∀ g ∈ SX, (fun y => g (e.symm y)) ∈ SY) :
    SY.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = SX := by
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro h
    have h3 := h1 _ h
    convert h3 using 1
    funext x
    rw [pbE_symm_apply]
    simp
  · intro h
    convert h2 g h using 1
    funext y
    exact pbE_symm_apply e g y

lemma map_addFun (p : ℕ) (e : X ≃+ Y) :
    (addFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = addFun R p X := by
  exact map_pbE_eq_of_addEquiv e _ _ (fun f hf => comp_mem_addFun p e hf) (fun g hg => comp_mem_addFun p e.symm hg)

lemma map_intFun (e : X ≃+ Y) :
    (intFun R Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = intFun R X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    have h : ∀ y : Y, ∃ r : R, algebraMap R C r = f y := hf
    show ∀ x : X, ∃ r : R, algebraMap R C r = f (e x)
    exact fun x => h (e x)
  · intro g hg
    have h : ∀ x : X, ∃ r : R, algebraMap R C r = g x := hg
    show ∀ y : Y, ∃ r : R, algebraMap R C r = g (e.symm y)
    exact fun y => h (e.symm y)

lemma map_pFun (p : ℕ) (e : X ≃+ Y) :
    (pFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = pFun R p X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hf ⊢
    exact fun x => hf (e x)
  · intro g hg
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hg ⊢
    exact fun y => hg (e.symm y)

lemma map_afFun (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (afFun p M).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      afFun p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
  show Submodule.map _ (M ⊓ addFun R p Y) = _ ⊓ addFun R p X
  rw [Submodule.map_inf, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

lemma map_linFun (p : ℕ) (e : X ≃+ Y) :
    (linFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = linFun R p X := by
  show Submodule.map _ (intFun R Y ⊓ addFun R p Y) = intFun R X ⊓ addFun R p X
  rw [Submodule.map_inf, map_intFun, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

private theorem nonempty_quotient_linearEquiv_map {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (φ : V ≃ₗ[R] W) (L A : Submodule R V) :
    Nonempty ((↥L ⧸ Submodule.comap L.subtype A) ≃ₗ[R]
      (↥(L.map (φ : V →ₗ[R] W)) ⧸ Submodule.comap (L.map (φ : V →ₗ[R] W)).subtype (A.map (φ : V →ₗ[R] W)))) := by
  refine ⟨Submodule.Quotient.equiv _ _ (φ.submoduleMap L) ?_⟩
  ext ⟨w, hw⟩
  constructor
  · rintro ⟨⟨v, hv⟩, hvA, hvw⟩
    have hw' : φ v = w := congrArg Subtype.val hvw
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hvA ⊢
    exact ⟨v, hvA, hw'⟩
  · intro h
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at h
    obtain ⟨v, hvA, rfl⟩ := h
    obtain ⟨v', hv'L, hv'⟩ := hw
    have hvv : v' = v := φ.injective hv'
    subst hvv
    exact ⟨⟨v', hv'L⟩, hvA, rfl⟩

lemma afQuot_equiv (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    Nonempty (AFQuot p M ≃ₗ[R]
      AFQuot p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)))) := by
  obtain ⟨f⟩ := nonempty_quotient_linearEquiv_map (pbE (C := C) (R := R) e) (linFun R p Y) (afFun p M ⊔ pFun R p Y)
  rw [map_linFun, Submodule.map_sup, map_afFun, map_pFun] at f
  exact ⟨f⟩

end

lemma exists_coord (p : ℕ) [Fact p.Prime] (N : Type) [AddCommGroup N] [Finite N]
    [Module (ZMod p) N] : ∃ n : ℕ, Nonempty ((Fin n → ZMod p) ≃+ N) :=
  have : Module.Finite (ZMod p) N := Module.Finite.of_finite
  ⟨_, ⟨(Module.finBasis (ZMod p) N).equivFun.symm.toAddEquiv⟩⟩

private theorem genAF_bot_of_span_monomials {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {N : Type} [AddCommGroup N] (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R (N → C))
    (y : ι → N → C) (hy : ∀ j, y j ∈ afFun p M) (S : Set (N → C))
    (hS : M = Submodule.span R S) (hgen : ∀ s ∈ S, ∃ α : ι → ℕ, s = ∏ j, y j ^ α j) :
    GenAF p M ⊥ := by
  have hinv : invFun M (⊥ : AddSubgroup N) = M := by
    ext g
    constructor
    · intro h
      exact (show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x from h).1
    · intro h
      show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x
      refine ⟨h, ?_⟩
      intro x k hk
      rw [AddSubgroup.mem_bot] at hk
      subst hk
      simp
  show invFun M ⊥ ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p (invFun M ⊥) : Set (N → C)))
  rw [hinv]
  have hsp : Submodule.span R S ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p M : Set (N → C))) := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨α, rfl⟩ := hgen s hs
    exact (Subalgebra.mem_toSubmodule _).mpr
      (Subalgebra.prod_mem _ (fun j _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (hy j)) _))
  intro g hg
  rw [hS] at hg
  exact hsp hg

theorem cnt_of (hcoord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  intro p _ C _ _ _ v R _ _ hvR hp N _ _ _ hN AA cA cN hA hC
  letI : Module (ZMod p) N := AddCommGroup.zmodModule hN
  obtain ⟨n, ⟨e⟩⟩ := exists_coord p N
  have hcard : Fintype.card (Fin n → ZMod p) = Fintype.card N := Fintype.card_congr e.toEquiv
  obtain ⟨f⟩ := afQuot_equiv (C := C) (R := R) p e AA.carrier
  have hA' : HasLen v R (AFQuot p (hopfPull e AA).carrier) cA := by
    obtain ⟨m, c, ⟨g⟩, hc⟩ := hA
    exact ⟨m, c, ⟨f.symm.trans g⟩, hc⟩
  have hC' : HasColen R v (hopfPull e AA).carrier cN := hasColen_map v e _ _ hC
  obtain ⟨hle, heq⟩ := hcoord p C v R hvR hp (Fin n) (hopfPull e AA) cA cN hA' hC'
  rw [hcard] at hle heq
  refine ⟨hle, fun hE => ?_⟩
  obtain ⟨x, hxj, hspan⟩ := heq hE
  refine genAF_bot_of_span_monomials p AA.carrier (fun j z => x j (e.symm z)) ?_
    ((⇑(pbE (C := C) (R := R) e.symm)) '' Set.range
      (fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)) ?_ ?_
  · intro j
    have hx' : x j ∈ (afFun p AA.carrier).map
        (pbE (C := C) (R := R) e : (N → C) →ₗ[R] ((Fin n → ZMod p) → C)) := by
      rw [map_afFun]
      exact hxj j
    have h2 := (Submodule.mem_map_equiv _).mp hx'
    convert h2 using 1
    funext z
    rw [pbE_symm_apply]
  · have h1 := Submodule.map_span (pbE (C := C) (R := R) e.symm : ((Fin n → ZMod p) → C) →ₗ[R] (N → C))
      (Set.range fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)
    rw [← hspan] at h1
    rw [← map_pbE_symm e AA.carrier]
    exact h1
  · rintro s ⟨_, ⟨α, rfl⟩, rfl⟩
    refine ⟨fun j => (α j).val, ?_⟩
    funext z
    rw [Finset.prod_apply]
    rfl

end PositivityTheory.HtPt.Ra
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FormMemLin
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

section
variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]

def formR (p : ℕ) (ι : Type) [Fintype ι] : (ι → R) →ₗ[R] ((ι → ZMod p) → R) where
  toFun l x := ∑ i, l i * ((x i).val : R)
  map_add' l l' := by ext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c l := by ext x; simp [Finset.mul_sum, mul_assoc]

variable (C) in

def toC (X : Type) : (X → R) →ₗ[R] (X → C) := (Algebra.linearMap R C).compLeft X

variable {R}

theorem mem_pInt {p : ℕ} {z : C} : z ∈ pInt (C := C) R p ↔ ∃ r : R, z = algebraMap R C r * p := by
  simp only [pInt, Submodule.mem_span_singleton, Algebra.smul_def]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

theorem afLat_eq (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R ((ι → ZMod p) → C)) :
    afLat p M = (M ⊔ pFun R p _).comap (toC C R _ ∘ₗ formR R p ι) := by
  ext l
  rw [Submodule.mem_comap, Submodule.mem_sup]
  change (∃ g ∈ M, ∀ x, g x - algebraMap R C (∑ i, l i * ((x i).val : R)) ∈ pInt R p) ↔ _
  have hf : (toC C R _ ∘ₗ formR R p ι) l = fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) := rfl
  rw [hf]
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) - g x, ?_, ?_⟩
    · rw [pFun, Submodule.mem_pi]
      intro x _
      have := neg_mem (h x)
      rwa [neg_sub] at this
    · funext x
      simp
  · rintro ⟨g, hg, z, hz, he⟩
    refine ⟨g, hg, fun x => ?_⟩
    have hx : z x ∈ pInt R p := (Submodule.mem_pi.mp hz) x (Set.mem_univ x)
    have e : g x - algebraMap R C (∑ i, l i * ((x i).val : R)) = - z x := by
      rw [← congrFun he x]
      simp
    rw [e]
    exact neg_mem hx

theorem form_mem_lin (p : ℕ) [NeZero p] {ι : Type} [Fintype ι] (l : ι → R) :
    (toC C R _ ∘ₗ formR R p ι) l ∈ linFun (C := C) R p (ι → ZMod p) := by
  rw [linFun, Submodule.mem_inf]
  have hf : (toC C R _ ∘ₗ formR R p ι) l = fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) := rfl
  rw [hf]
  refine ⟨fun x => ⟨∑ i, l i * ((x i).val : R), rfl⟩, ?_⟩
  intro x y
  rw [mem_pInt]
  refine ⟨-∑ i, l i * ((((x i).val + (y i).val) / p : ℕ) : R), ?_⟩
  have key : ∀ i, (((x i + y i).val : ℕ) : R) = ((x i).val : R) + (y i).val - p * ((((x i).val + (y i).val) / p : ℕ) : R) := by
    intro i
    rw [ZMod.val_add, eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div, Nat.cast_add]
  simp only [Pi.add_apply, key]
  simp only [← map_sub, ← map_neg, ← map_natCast (algebraMap R C), ← map_mul]
  congr 1
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem add_mem_pFun {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    {h : (ι → ZMod p) → C} (hh : h ∈ addFun R p (ι → ZMod p))
    (h1 : ∀ i, h (Pi.single i 1) ∈ pInt (C := C) R p) : h ∈ pFun R p (ι → ZMod p) := by
  have h0 : h 0 ∈ pInt (C := C) R p := by
    have := neg_mem (hh 0 0)
    simpa using this
  let S : AddSubmonoid (ι → ZMod p) :=
    { carrier := {x | h x ∈ pInt (C := C) R p}
      add_mem' := by
        intro a b ha hb
        have e : h (a + b) = (h (a + b) - h a - h b) + h a + h b := by ring
        show h (a + b) ∈ pInt (C := C) R p
        rw [e]
        exact add_mem (add_mem (hh a b) ha) hb
      zero_mem' := h0 }
  have hall : ∀ x, x ∈ S := by
    intro x
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun i _ => ?_
    have e : Pi.single i (x i) = (x i).val • (Pi.single i (1 : ZMod p) : ι → ZMod p) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_apply, hj]
    rw [e]
    exact nsmul_mem (show (Pi.single i (1 : ZMod p) : ι → ZMod p) ∈ S from h1 i) _
  rw [pFun, Submodule.mem_pi]
  intro x _
  exact hall x

end

theorem aflat_fg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), (afLat p AA.carrier).FG := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : ValuationRing R :=
    { cond' := fun a b => by
        rcases le_total (v (algebraMap R C a)) (v (algebraMap R C b)) with h | h
        · obtain ⟨c, hc⟩ := hv.dvd_of_le h
          exact ⟨c, Or.inr hc.symm⟩
        · obtain ⟨c, hc⟩ := hv.dvd_of_le h
          exact ⟨c, Or.inl hc.symm⟩ }
  rw [afLat_eq, Submodule.comap_comp]
  apply comap_fg_of_valuationRing
  have hinj : Function.Injective (toC C R (ι → ZMod p)) := by
    intro f g h
    funext x
    exact hv.hom_inj (congrFun h x)
  apply Submodule.fg_of_fg_map_injective (toC C R (ι → ZMod p)) hinj
  have hle : AA.carrier ⊔ pFun R p (ι → ZMod p) ≤ LinearMap.range (toC C R (ι → ZMod p)) := by
    apply sup_le
    · intro f hf
      have hi := AA.le_int hf
      choose r hr using hi
      exact ⟨r, funext fun x => hr x⟩
    · intro f hf
      rw [pFun, Submodule.mem_pi] at hf
      choose r hr using fun x => mem_pInt.mp (hf x (Set.mem_univ x))
      refine ⟨fun x => r x * p, funext fun x => ?_⟩
      rw [hr x]
      simp [toC]
  rw [Submodule.map_comap_eq, inf_eq_right.mpr hle]
  apply Submodule.FG.sup
  · obtain ⟨B, _, hB⟩ := AA.lat
    rw [hB]
    exact Submodule.fg_span (Set.finite_range _)
  · have hP : pFun R p (ι → ZMod p) = Submodule.map ((p : R) • toC C R (ι → ZMod p)) ⊤ := by
      ext f
      simp only [Submodule.mem_map, Submodule.mem_top, true_and]
      rw [pFun, Submodule.mem_pi]
      constructor
      · intro hf
        choose r hr using fun x => mem_pInt.mp (hf x (Set.mem_univ x))
        refine ⟨r, funext fun x => ?_⟩
        rw [hr x]
        simp [toC, Algebra.smul_def, mul_comm]
      · rintro ⟨r, rfl⟩ x _
        rw [mem_pInt]
        exact ⟨r x, by simp [toC, Algebra.smul_def, mul_comm]⟩
    rw [hP]
    exact Submodule.FG.map _ Module.Finite.fg_top

theorem afquot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let φ := toC C R (ι → ZMod p) ∘ₗ formR R p ι
  let K := Submodule.comap (linFun (C := C) R p (ι → ZMod p)).subtype (afFun p AA.carrier ⊔ pFun (C := C) R p (ι → ZMod p))
  let ψ : (ι → R) →ₗ[R] linFun (C := C) R p (ι → ZMod p) := LinearMap.codRestrict _ φ (fun l => form_mem_lin p l)
  let f := K.mkQ ∘ₗ ψ
  have hpf : pFun (C := C) R p (ι → ZMod p) ≤ addFun (C := C) R p (ι → ZMod p) := by
    intro z hz x y
    rw [pFun, Submodule.mem_pi] at hz
    exact sub_mem (sub_mem (hz _ (Set.mem_univ _)) (hz _ (Set.mem_univ _))) (hz _ (Set.mem_univ _))
  have hker : afLat p AA.carrier = LinearMap.ker f := by
    ext l
    rw [LinearMap.mem_ker, afLat_eq, Submodule.mem_comap]
    change _ ↔ Submodule.Quotient.mk (ψ l) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    change φ l ∈ AA.carrier ⊔ pFun (C := C) R p _ ↔ φ l ∈ afFun p AA.carrier ⊔ pFun (C := C) R p _
    constructor
    · intro h
      obtain ⟨g, hg, z, hz, he⟩ := Submodule.mem_sup.mp h
      have hadd : φ l ∈ addFun (C := C) R p (ι → ZMod p) := (Submodule.mem_inf.mp (form_mem_lin p l)).2
      have hg' : g ∈ addFun (C := C) R p (ι → ZMod p) := by
        have : g = φ l - z := by rw [← he]; abel
        rw [this]
        exact sub_mem hadd (hpf hz)
      exact Submodule.mem_sup.mpr ⟨g, Submodule.mem_inf.mpr ⟨hg, hg'⟩, z, hz, he⟩
    · intro h
      exact (sup_le_sup_right inf_le_left _ : afFun p AA.carrier ⊔ pFun (C := C) R p _ ≤ AA.carrier ⊔ pFun (C := C) R p _) h
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.mkQ_surjective K q
    have hh' := Submodule.mem_inf.mp hh
    choose l hl using fun i => hh'.1 (Pi.single i (1 : ZMod p))
    refine ⟨l, ?_⟩
    show Submodule.Quotient.mk (ψ l) = Submodule.Quotient.mk ⟨h, hh⟩
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    apply Submodule.mem_sup_right
    change φ l - h ∈ pFun (C := C) R p (ι → ZMod p)
    apply add_mem_pFun
    · exact sub_mem (Submodule.mem_inf.mp (form_mem_lin p l)).2 hh'.2
    · intro i
      have e : φ l (Pi.single i 1) = algebraMap R C (l i) := by
        show algebraMap R C (∑ j, l j * (((Pi.single i (1 : ZMod p) : ι → ZMod p) j).val : R)) = _
        simp [Pi.single_apply, apply_ite, ZMod.val_one]
      rw [Pi.sub_apply, e, hl i, sub_self]
      exact zero_mem _
  exact ⟨((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective f hsurj)).symm⟩

end PositivityTheory.HtPt.Rh
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace Pull

variable {B B' : Type} [CommRing B] [CommRing B'] {Y Z : Scheme.{0}}

theorem valAt_comp (y : Spec (CommRingCat.of B) ⟶ Y) (φ : Y ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ W) (f : Γ(Z, W)) :
    valAt (y ≫ φ) W h f = valAt y (φ ⁻¹ᵁ W) h ((φ.app W).hom f) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem valAt_spec (φ : B →+* B') (y : Spec (CommRingCat.of B) ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ y) ⁻¹ᵁ W) (f : Γ(Y, W)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ y) W h' f = φ (valAt y W h f) := by
  have e : (Spec.map (CommRingCat.ofHom φ) ≫ y).appLE W ⊤ h' =
      y.appLE W ⊤ h ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    have := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) y W ⊤ ⊤ h le_top
    rw [← this]
    simp [Scheme.Hom.appLE]
    rfl
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  simp only [valAt, e]
  exact congrArg (fun z => z.hom ((y.appLE W ⊤ h).hom f)) n

theorem valAt_congr {B : Type} [CommRing B] {Y : Scheme.{0}} {y y' : Spec (CommRingCat.of B) ⟶ Y} (e : y = y') (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y' ⁻¹ᵁ W) (f : Γ(Y, W)) : valAt y W h f = valAt y' W h' f := by
  subst e; rfl

end Pull

theorem reg_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ f g' ⟨U, hU, s, hs⟩
  refine ⟨F ⁻¹ᵁ U, hU, (F.app U).hom s, fun t h => ?_⟩
  have e := GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hF κ hκ t
  have h1 : ⊤ ≤ ((Γ'.pt t).left ≫ F) ⁻¹ᵁ U := h
  have h2 : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := e ▸ h1
  have h3 : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun z _ => by
    have hz : z = Spec.map (CommRingCat.ofHom κ) (IsLocalRing.closedPoint (FractionRing R')) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [hz]
    exact h2 (by trivial)
  refine (Pull.valAt_comp _ F U h1 s).symm.trans ((Pull.valAt_congr e U h1 h2 s).trans ?_)
  rw [Pull.valAt_spec κ _ U h3, hs t h3]

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RaChar
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

theorem charmem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA ψ
  obtain ⟨B, hB, hAA⟩ := AA.lat
  rw [hAA, ← dualLat_dualLat_spanCols B hB, ← hAA]
  intro u hu
  obtain ⟨r, hr⟩ := hv.exists_of_le_one
    (valuation_fourier_le_one v hv (fun _ : Unit => ψ) AA hu ())
  refine ⟨r, hr.trans ?_⟩
  rw [fourier_apply']
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end PositivityTheory.HtPt.Ra
end
end

