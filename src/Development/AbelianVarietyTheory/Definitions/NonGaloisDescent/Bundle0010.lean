import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def Fil (a : ℤ) : Set P.R.BdR := ((P.PD (botExt l)).Fil a : Set P.R.BdR)

def fr (l : ℕ) [Fact l.Prime] (m : ℕ) : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l) := ((frobUr l ^ m : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l))

def kd : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (algebraMap (Om l) P.R.BdR).comp (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))

def ks : ↥(MaximalUnramifiedExtension l) →+* Bst P := (Polynomial.C : P.R.B →+* Bst P).comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)

def ev (m : ℕ) (b : P.R.B) : P.R.BdR := P.ιB (P.φB^[m] b)

def tz (a : ℤ) : P.R.BdR := P.ιB (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B)

variable {n : Type} [Fintype n] [DecidableEq n]

def UnitM (U : GL n P.R.BdR) : Prop :=
  (∀ i j, (U : Matrix n n P.R.BdR) i j ∈ Fil P 0) ∧ ∀ i j, ((U⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i j ∈ Fil P 0

variable {K : FinExt l}

structure IsRat (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop where

  pos : 0 < r

  le : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1

  rat : ∀ g i j, fr l r ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j

  cont : ∀ i j, Continuous fun g => (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)

def matD (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) : Matrix n n P.R.BdR :=
  (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map fun c => kd P (fr l m c)

def AdmDR (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∀ m : ℕ, ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K),
    matD P ρ m g * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q

def Framed {r : ℕ} (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) : Prop :=
  ∀ m : Fin r, ∃ U : GL n P.R.BdR, UnitM P U ∧ ∀ g : ↥(GK K),
    matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])

def AdmSt (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∃ (K' : FinExt l) (hK : K.1 ≤ K'.1) (Q : GL n (Bst P)), ∀ g : ↥(GK K'),
    (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q

def Splits (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∃ (s : Finset n) (p : GL n ↥(MaximalUnramifiedExtension l)), s.Nonempty ∧ s ≠ Finset.univ ∧
    (∀ i j, fr l r ((p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) ∧
    ∀ g i j, i ∉ s → j ∈ s → ((p⁻¹ * ρ g * p : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) i j = 0

def eps {α : Type} [DecidableEq α] (x y z : α) : ℤ := if z = x then -1 else if z = y then 1 else 0

variable {P} in

def Plus {AI : LocAinf l P} (T : LocTied l P AI) (b : P.R.B) : Prop :=
  ∃ (N : ℕ) (x : Formalism.Per.Acris l), T.eB ((l : P.R.B) ^ N * b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) x

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisExportOfMatrixDetBounds
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwSys.Test

section Ord
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem ordHyp_X (l M : ℕ) :
    OrdHyp O l M 1 1 0 (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) := by
  refine ⟨MvPolynomial.X (Sum.inl 0), 1, ?_, ?_, 1, fun _ => 1, by simp, fun _ => le_rfl, by simp⟩
  · apply Ideal.subset_span
    left
    exact ⟨0, by ring⟩
  · simp

theorem addVal_le_of_ordHyp {l M R v : ℕ} (hl : l ≠ 0) {f : MvPolynomial (Fin R ⊕ Fin R) O}
    (h : OrdHyp O l M R 0 v f) : IsDiscreteValuationRing.addVal O (f.coeff 0) ≤ v := by
  obtain ⟨Dd, g, h1, h2, u, n, hu, hn, h3⟩ := h
  have hn0 : ∀ i, n i = 0 := fun i => Nat.le_zero.1 (hn i)
  have e1 : MvPolynomial.constantCoeff (f - Dd * g) = 0 := by
    have : Ideal.span (Set.range (fun i : Fin R => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
      Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) ≤
        RingHom.ker MvPolynomial.constantCoeff := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> simp
    exact this h1
  have e2 : MvPolynomial.constantCoeff (Dd.map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i) = 0 := by
    have : Ideal.span (Set.range fun q =>
          (MvPolynomial.X q : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M)) ≤
        RingHom.ker MvPolynomial.constantCoeff := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [hl]
    exact this h3
  simp only [hn0, pow_zero, Finset.prod_const_one, mul_one, map_sub, MvPolynomial.constantCoeff_map, sub_eq_zero] at e2
  have hD : IsUnit (MvPolynomial.constantCoeff Dd) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, e2]
    exact hu
  rw [map_sub, map_mul, sub_eq_zero] at e1
  have : f.coeff 0 = MvPolynomial.constantCoeff Dd * g.coeff 0 := e1
  rw [this, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hD, zero_add]
  exact h2

theorem not_ordHyp_X {l M v : ℕ} (hl : l ≠ 0) : ¬ OrdHyp O l M 1 0 v (MvPolynomial.X (Sum.inr 0)) := by
  intro h
  have := addVal_le_of_ordHyp O hl h
  simp at this

end Ord

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in

theorem exists_isCoord (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (M : ℕ) : ∃ d, IsCoord Y i M d := by
  let c : ∀ (Q : Finset (PlE D.host)) (P : PlE D.host), P ∈ Q → (GE N →* Multiplicative (ZMod (X.l i ^ M))) :=
    fun Q P hP => (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : ↥Q => ZMod (X.l i ^ M)) ⟨P, hP⟩)).comp
      (Y.delU i Q M)
  refine ⟨fun P => if h : ∃ Q, ConjCl (D := D) Q ∧ P ∈ Q then c h.choose P h.choose_spec.2 else 1, ?_⟩
  intro Q hQ P hP σ
  have h : ∃ Q, ConjCl (D := D) Q ∧ P ∈ Q := ⟨Q, hQ, hP⟩
  simp only [dif_pos h]
  have hU : ConjCl (D := D) (Q ∪ h.choose) := by
    intro P hP P' hc
    rcases Finset.mem_union.1 hP with h1 | h1
    · exact Finset.mem_union_left _ (hQ P h1 P' hc)
    · exact Finset.mem_union_right _ (h.choose_spec.1 P h1 P' hc)
  rw [Y.delU_res i M Q (Q ∪ h.choose) Finset.subset_union_left hQ hU σ P hP]
  exact (Y.delU_res i M h.choose (Q ∪ h.choose) Finset.subset_union_right h.choose_spec.1 hU σ P h.choose_spec.2).symm

open Classical in
theorem toLam_surjective (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : Function.Surjective (toLam X i M ι) := by
  have hl : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  have key : ∀ g : Del X i M ι, MonoidAlgebra.of (X.O0 i) (Del X i M ι) g ∈ (toLam X i M ι).range := by
    intro g
    refine ⟨∏ q, (1 + MvPolynomial.X q) ^ (Multiplicative.toAdd g q).val, ?_⟩
    simp only [toLam, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow, map_add, map_one, MvPolynomial.aeval_X, add_sub_cancel]
    simp only [← map_pow, ← map_prod]
    congr 1
    apply Multiplicative.toAdd.injective
    ext q
    simp only [toAdd_prod, toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    simp [nsmul_eq_mul]
  intro x
  have : x ∈ (toLam X i M ι).range := by
    induction x using MonoidAlgebra.induction_on with
    | of g => exact key g
    | add f g hf hg => exact add_mem hf hg
    | smul r f hf => exact Subalgebra.smul_mem _ hf r
  exact this

theorem galois_export_of_matrix_det_bounds (bkP : BKPh X) (hS : ThmS bkP) (hS4 : SelmerLengthsByDeterminant bkP) (h3 : ResidualBoundOddPrimes bkP) (hC : ThmC bkP) : GaloisSideTwistedSelmerAuxiliaryPrimes bkP := by
  intro i T hT
  have hO : OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)) := by
    rcases Nat.eq_zero_or_pos (nu X i) with h | h
    · rw [h, pow_zero, IsDiscreteValuationRing.addVal_one]
      exact h3 i h
    · exact hC i h
  obtain ⟨R, Dd, M₀, h⟩ := hO T hT
  refine ⟨R, Dd, max M₀ 1, le_max_right _ _, fun M hM H S d hd z hz H' h1 h2 A => ?_⟩
  obtain ⟨P, hA, hSt, hF⟩ := h M (le_of_max_le_left hM) H S d hd z hz H' h1 h2 A
  refine ⟨P, hA, hSt, fun s hs Q hQ => ?_⟩
  have hA0 : SlopeTestRemainingChoices X i M ∅ P (fun q => d (P q)) :=
    ⟨fun q v hv => by
      obtain ⟨a, b, c, d', -, f⟩ := hA.1 q v hv
      exact ⟨a, b, c, d', by simp, f⟩, hA.2⟩
  obtain ⟨a, Φ, hΦ, -⟩ := hS i s (hT s hs) M _ P _ Q (le_of_max_le_right hM) hA0 hQ
  obtain ⟨F, hFd⟩ := toLam_surjective i M (Fin R ⊕ Fin R) Φ.det
  exact ⟨F, hS4 i s M _ P _ Q (le_of_max_le_right hM) hA0 hQ a Φ hΦ F hFd, hF s hs Q hQ a Φ hΦ F hFd⟩

end GlobalTheory.TwSys.Test

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.SelFun

def Tors (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (B : Type) [AddCommGroup B] [Module Λ B] : Prop :=
  ∀ b : B, ∃ n : ℕ, ∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, x • b = 0

section Maps

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  {B B' : Type} [AddCommGroup B] [Module Λ B] [AddCommGroup B'] [Module Λ B']

theorem repOn_map (f : B →ₗ[Λ] B') (g : Γ) (m : Fin r → B) :
    f.compLeft (Fin r) (repOn ρ κ B g m) = repOn ρ κ B' g (f.compLeft (Fin r) m) := by
  funext a
  simp [repOn, matAct, map_sum, Finset.smul_sum]

variable [TopologicalSpace Γ] [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace B'] [DiscreteTopology B']

def h1Map (f : B →ₗ[Λ] B') : H1 (repOn ρ κ B) →ₗ[Λ] H1 (repOn ρ κ B') :=
  mapH1 _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology (repOn_map ρ κ f)

def h1MapSubgroup (U : Subgroup Γ) (f : B →ₗ[Λ] B') :
    H1 ((repOn ρ κ B).comp U.subtype) →ₗ[Λ] H1 ((repOn ρ κ B').comp U.subtype) :=
  mapH1 _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology (fun g m => repOn_map ρ κ f g.1 m)

end Maps

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
  (Q : Finset (PlE D.host))

def Setup : Prop :=
  GalHyp bkP i s ∧ IsLocalHom (algebraMap (X.O0 i) Λ) ∧ Module.Finite (X.O0 i) Λ ∧
    IsOpen (κ.ker : Set (GE N)) ∧ (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) ∧ TrivAbove κ (X.l i) ∧
    (∀ v ∈ Q, v ∉ placesOver D.host.E (X.l i)) ∧
    ∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, κ σ = 1

def SelMaps : Prop :=
  ∀ (B B' : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[Λ] B'),
    (selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ f) ≤ selOn bkP i (Tgl i s) κ B' Q

def NoInv : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    H0 (repOn (Tgl i s) κ B) = ⊥

def LocSat : Prop :=
  ∀ v ∈ placesOver D.host.E (X.l i),
  ∀ (B' B : Type) [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ f : B' →ₗ[Λ] B, Function.Injective f → ∀ y : H1 ((repOn (Tgl i s) κ B').comp (DecV N v).subtype),
      h1MapSubgroup (Tgl i s) κ (DecV N v) f y ∈ bkOn bkP i (Tgl i s) κ B v → y ∈ bkOn bkP i (Tgl i s) κ B' v

def SelLeft : Prop :=
  ∀ (B' B B'' : Type) [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B''] [Module Λ B''] [TopologicalSpace B''] [DiscreteTopology B''], Tors Λ B → Tors Λ B'' →
    ∀ (f : B' →ₗ[Λ] B) (g : B →ₗ[Λ] B''), Function.Injective f → Function.Exact f g →
      Function.Injective (h1Map (Tgl i s) κ f) ∧
      ∀ y ∈ selOn bkP i (Tgl i s) κ B Q, h1Map (Tgl i s) κ g y = 0 →
        ∃ x ∈ selOn bkP i (Tgl i s) κ B' Q, h1Map (Tgl i s) κ f x = y

def SelColim : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ y ∈ selOn bkP i (Tgl i s) κ B Q, ∃ B' : Submodule Λ B, B'.FG ∧
      ∃ x ∈ selOn bkP i (Tgl i s) κ B' Q, h1Map (Tgl i s) κ B'.subtype x = y

def LocCount : Prop :=
  ∀ (K : Type) [AddCommGroup K] [Module Λ K] [TopologicalSpace K] [DiscreteTopology K], IsSimpleModule Λ K →
    ∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (bkOn bkP i (Tgl i s) κ K v) =
      (∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype))) *
        Nat.card K ^ (D.R.f * D.R.r)

def SelObs : Prop :=
  ∀ (K B B'' : Type) [AddCommGroup K] [Module Λ K] [TopologicalSpace K] [DiscreteTopology K]
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B''] [Module Λ B''] [TopologicalSpace B''] [DiscreteTopology B''], IsSimpleModule Λ K → Tors Λ B →
    ∀ (f : K →ₗ[Λ] B) (g : B →ₗ[Λ] B''), Function.Injective f → Function.Exact f g → Function.Surjective g →
      Finite (selOn bkP i (Tgl i s) κ K Q) ∧
      Finite (↥(selOn bkP i (Tgl i s) κ B'' Q) ⧸ ((selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ g)).comap
        (selOn bkP i (Tgl i s) κ B'' Q).subtype) ∧
      Nat.card (↥(selOn bkP i (Tgl i s) κ B'' Q) ⧸ ((selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ g)).comap
        (selOn bkP i (Tgl i s) κ B'' Q).subtype) ≤ Nat.card (selOn bkP i (Tgl i s) κ K Q)

open CategoryTheory in

def KernelRep : Prop :=
  ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    [Finite (IsLocalRing.ResidueField Λ)] (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
    (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ y : F.obj B, ∃ B' : Submodule Λ B, B'.FG ∧
      y ∈ LinearMap.range (F.map (ModuleCat.ofHom B'.subtype)).hom) →
    (∀ (K B B'' : ModuleCat.{0} Λ), IsSimpleModule Λ K → Tors Λ B → ∀ (f : K ⟶ B) (g : B ⟶ B''),
      Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
      Finite (F.obj K) ∧ Finite (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ∧
        Nat.card (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ≤ Nat.card (F.obj K)) →
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) Λ), (∀ b c, ¬ IsUnit (Φ b c)) ∧
      ∃ e : ∀ B : ModuleCat.{0} Λ, Tors Λ B → (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[Λ] F.obj B),
        ∀ (B B' : ModuleCat.{0} Λ) (hB : Tors Λ B) (hB' : Tors Λ B') (f : B ⟶ B')
          (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ))),
          (∀ c, x'.1 c = f.hom (x.1 c)) → e B' hB' x' = (F.map f).hom (e B hB x)

end GlobalTheory.SelFun
end
end

