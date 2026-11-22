import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect

section Abstract

variable {F Y : Type} [Field F] [AddCommGroup Y] [Module F Y] {c : ℕ}

def IsFrame (X : Submodule F Y) (a : Fin c → Y) : Prop :=
  LinearIndependent F a ∧ IsCompl X (Submodule.span F (Set.range a))

def flag (X : Submodule F Y) (a : Fin c → Y) (i : Fin c) : Submodule F Y :=
  X ⊔ Submodule.span F (a '' {l | l < i})

def IsUnip (X : Submodule F Y) (a : Fin c → Y) (n : Y ≃ₗ[F] Y) : Prop :=
  (∀ x ∈ X, n x = x) ∧ (∀ i : Fin c, i.1 = 0 → n (a i) = a i) ∧ ∀ i : Fin c, n (a i) - a i ∈ flag X a i

def IsExtOf (X : Submodule F Y) (a : Fin c → Y) (γ : X ≃ₗ[F] X) (g : Y ≃ₗ[F] Y) : Prop :=
  (∀ x : X, g x = (γ x : Y)) ∧ ∀ i, g (a i) = a i

def IsSemidirect (X : Submodule F Y) (a : Fin c → Y) (r : Y ≃ₗ[F] Y) : Prop :=
  ∃ (γ : X ≃ₗ[F] X) (g n : Y ≃ₗ[F] Y), IsExtOf X a γ g ∧ IsUnip X a n ∧ r = g * n

variable {O : Type} [CommRing O] [Algebra O F] [Module O Y] [IsScalarTower O F Y]

def moveBy (r : Y ≃ₗ[F] Y) (Λ : Submodule O Y) : Submodule O Y :=
  Λ.map (r.toLinearMap.restrictScalars O)

def normalForm (F : Type) [Field F] [Module F Y] [Algebra O F] (q : O) (M : Submodule O Y) (a : Fin c → Y)
    (e : Fin c → ℤ) (z : Y) : Submodule O Y :=
  M ⊔ ⨆ i : Fin c, Submodule.span O {(algebraMap O F q) ^ (e i) • (a i + if i.1 = 0 then z else 0)}

def inY (X : Submodule F Y) (L : Submodule O X) : Submodule O Y :=
  L.map (X.subtype.restrictScalars O)

end Abstract

def LatticeNormalForm : Prop :=
  ∀ (O F Y : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y]
    (q : O), Irreducible q →
    ∀ (c : ℕ) (X : Submodule F Y) (a : Fin c → Y), IsFrame X a →
    ∀ (L : Submodule O X), Submodule.IsLattice F L →
    ∀ (Λ : Submodule O Y), Submodule.IsLattice F Λ →
      ∃ (r : Y ≃ₗ[F] Y) (e : Fin c → ℤ) (z : Y), IsSemidirect X a r ∧ z ∈ X ∧
        moveBy r Λ = normalForm F q (inY X L) a e z

def LatticeNormalFormUnip : Prop :=
  ∀ (O F Y : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y]
    (q : O), Irreducible q →
    ∀ (c : ℕ) (X : Submodule F Y) (a : Fin c → Y), IsFrame X a →
    ∀ (Λ : Submodule O Y), Submodule.IsLattice F Λ →
      ∃ (n : Y ≃ₗ[F] Y) (e : Fin c → ℤ) (z : Y), IsUnip X a n ∧ z ∈ X ∧
        moveBy n Λ = normalForm F q (Λ ⊓ X.restrictScalars O) a e z

open Formalism.L2.Col in

def LatticeNormalFormCoord : Prop :=
  ∀ (O F : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    (q : O), Irreducible q →
    ∀ (n c : ℕ) (L : Submodule O (Fin n → F)), Submodule.IsLattice F L →
    ∀ (Λ : Submodule O (Fin (n + c) → F)), Submodule.IsLattice F Λ →
      ∃ r ∈ Loc.R1 F n c, ∃ (e : Fin c → ℤ) (z : Fin n → F),
        moveBy r Λ = normalForm F q (L.map ((Loc.inX F n c).restrictScalars O))
          (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) e (Loc.inX F n c z)

section Basic₂

variable {F Y : Type} [Field F] [AddCommGroup Y] [Module F Y] {c : ℕ}

theorem isUnip_one (X : Submodule F Y) (a : Fin c → Y) : IsUnip X a 1 :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun i => by
    show a i - a i ∈ _
    rw [sub_self]
    exact zero_mem _⟩

example {O : Type} [CommRing O] [Algebra O F] [Module O Y] (q : O) (M : Submodule O Y) (a : Fin (c + 1) → Y)
    (e : Fin (c + 1) → ℤ) (z : Y) : (algebraMap O F q) ^ (e 0) • (a 0 + z) ∈ normalForm F q M a e z := by
  refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem 0 (Submodule.subset_span ?_))
  simp

example : IsFrame (F := ℚ) (LinearMap.range (LinearMap.inl ℚ ℚ ℚ)) (fun _ : Fin 1 => ((0, 1) : ℚ × ℚ)) := by
  refine ⟨by simp [linearIndependent_unique_iff], ?_⟩
  have h : Submodule.span ℚ (Set.range (fun _ : Fin 1 => ((0, 1) : ℚ × ℚ))) = LinearMap.range (LinearMap.inr ℚ ℚ ℚ) := by
    ext x
    simp only [Set.range_const, Submodule.mem_span_singleton, LinearMap.mem_range, LinearMap.coe_inr]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, by simp⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by simp⟩
  rw [h]
  exact LinearMap.isCompl_range_inl_inr

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.NormalFormInclusion
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalFormInclusion

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def nfVec (q : ℕ) (n c : ℕ) (ex : Fin c → ℤ) (z : Sp E n) (i : Fin c) : Sp E (n + c) :=
  ((q : E) ^ ex i) • (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0)

def nfLat (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (n c : ℕ) (ex : Fin c → ℤ) (z : Sp E n) : Submodule (𝓞 E) (Sp E (n + c)) :=
  (stdAt E n P).map ((Loc.inX E n c).restrictScalars (𝓞 E)) ⊔
    (stdAt E c P).map ((Fintype.linearCombination E (nfVec q n c ex z)).restrictScalars (𝓞 E))

end Lattice

variable {X : Fields} {R : Ranks}

def NF (Pr : Primes X) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  ∃ (ex : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)),
    (∀ i, -(j : ℤ) ≤ ex i ∧ ex i ≤ 0) ∧
    z ∈ stdAt X.E (R.N j) P ∧
    gmap h (lamYat (Pr := Pr) (R := R) j P) = nfLat P (qOf P) (R.N j) (cOf R j) ex z

def NFIncl (X : Fields) (Pr : Primes X) (R : Ranks) : Prop :=
  ∀ (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : AutY X R j, NF Pr j P h →
    ∀ k ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P),
      lamYat (Pr := Pr) (R := R) j P ≤ gmap (h * k : AutY X R j) (lamYat (Pr := Pr) (R := R) j P) ∧
      ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, ((qOf P : X.E) ^ j) • (h * k : AutY X R j) x ∈ lamYat (Pr := Pr) (R := R) j P

section Chain

variable {Pr : Primes X} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def PsiReads (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  ∃ d : ℕ,
    (∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ d * x) → IntAt P.1 ((qOf P.1 : X.E) ^ d * y) →
      cst.psi P (x + y) = cst.psi P x * cst.psi P y) ∧
    ∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, ((qOf P.1 : X.E) ^ d) • h x ∈ lamYat (Pr := Pr) (R := R) j P.1

def RepExists : Prop :=
  cst.Ok → ∀ i : ℕ, i + 1 ≤ R.m - 2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → DegOne P.1 →
    ∀ hal : AutY X R i, NF Pr i P.1 hal →
    ∀ h h₁ : AutY X R (i + 1), SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h₁ → PsiReads sel mu cst (i + 1) P h₁ →
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h₁ →
      ∃ h' : AutY X R (i + 1), SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' ∧ NF Pr (i + 1) P.1 h'

def IdxNF (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m - 2 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → NF Pr j P.1 (L.h j b P)

def ChoiceExists : Prop :=
  (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → DegOne P.1) →
  ∀ (G : ChGlob X R.m) (m2 : ℕ) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))), L.Ok Ch sel mu cst G m2 →
    ∃ (h' : ∀ j, L.β j → rowSG Pr sel mu → AutY X R j)
      (lq : ∀ j, L.β j → LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))) (A₀ B₀ : ℕ),
      (∀ j b P, SameDC (Pr := Pr) cst.sharp j P.1 (L.h j b P) (h' j b P)) ∧
      (∀ j b (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → h' j b P = L.h j b P) ∧
      IdxNF sel mu { L with h := h', levQ := lq } ∧
      ∀ A' B' : ℕ, A₀ ≤ A' → B₀ ≤ B' →
        ChIdx.Ok Ch sel mu { cst with A := A', B := B' } { L with h := h', levQ := lq } G m2

end Chain

def NormalFormAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks), NFIncl X Pr R ∧
    ∀ (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
      (cst : LocCst X (rowSG Pr sel mu)), RepExists Ch sel mu cst ∧ ChoiceExists Ch sel mu cst

theorem nf_one (Pr : Primes X) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∉ Pr.vGs) : NF Pr j P (1 : AutY X R j) := by
  classical
  refine ⟨fun _ => 0, 0, fun _ => ⟨by simp, le_rfl⟩, zero_mem _, ?_⟩
  have hL : ∀ y, y ∈ lamYat (Pr := Pr) (R := R) j P ↔ ∀ l, IntAt P (y l) := by
    intro y
    unfold lamYat LocE.lamY LocE.sclLat stdAt
    rw [if_neg hP, Submodule.mem_comap, mem_localization_standardLattice]
    refine forall_congr' fun l => ?_
    simp [LocE.scE]
  have hg : gmap (1 : AutY X R j) (lamYat (Pr := Pr) (R := R) j P) = lamYat (Pr := Pr) (R := R) j P := by
    ext y
    simp [gmap, Submodule.mem_map]
  have h0 : IntAt P (0 : X.E) := by simpa using IntAt.coe P 0
  have hc : ∀ (s : Fin (cOf R j) → X.E) (l : Fin (R.N j + cOf R j)),
      (Fintype.linearCombination X.E (nfVec (qOf P) (R.N j) (cOf R j) (fun _ => 0) (0 : Sp X.E (R.N j))) s) l =
        if h : R.N j ≤ l.1 then s ⟨l.1 - R.N j, by have := l.2; omega⟩ else 0 := by
    intro s l
    rw [Fintype.linearCombination_apply, Finset.sum_apply]
    simp only [nfVec, zpow_zero, one_smul, map_zero, ite_self, add_zero, Pi.smul_apply, Loc.eN, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨l.1 - R.N j, by have := l.2; omega⟩]
      · rw [if_pos (by simp; omega)]
      · intro b _ hb
        rw [if_neg]
        intro e
        exact hb (Fin.ext (by simp; omega))
      · simp
    · exact Finset.sum_eq_zero fun b _ => if_neg (by omega)
  have hx : ∀ (x : Sp X.E (R.N j)) (l : Fin (R.N j + cOf R j)),
      Loc.inX X.E (R.N j) (cOf R j) x l = if h : l.1 < R.N j then x ⟨l.1, h⟩ else 0 := by
    intro x l
    unfold Loc.inX
    rw [LinearMap.pi_apply]
    split_ifs <;> simp
  rw [hg]
  apply le_antisymm
  · intro y hy
    rw [hL] at hy
    refine Submodule.mem_sup.2 ⟨Loc.inX X.E (R.N j) (cOf R j) (fun i => y (Fin.castAdd _ i)), ⟨_, ?_, rfl⟩,
      Fintype.linearCombination X.E (nfVec (qOf P) (R.N j) (cOf R j) (fun _ => 0) (0 : Sp X.E (R.N j))) (fun i => y (Fin.natAdd _ i)),
      ⟨_, ?_, rfl⟩, ?_⟩
    · exact (mem_localization_standardLattice P _).2 fun i => hy _
    · exact (mem_localization_standardLattice P _).2 fun i => hy _
    · funext l
      rw [Pi.add_apply, hx, hc]
      by_cases h : l.1 < R.N j
      · rw [dif_pos h, dif_neg (by omega), add_zero]
        rfl
      · rw [dif_neg h, dif_pos (by omega), zero_add]
        congr 1
        exact Fin.ext (by simp; omega)
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, hx', rfl⟩
      rw [hL]
      intro l
      have := (mem_localization_standardLattice P _).1 hx'
      rw [LinearMap.restrictScalars_apply, hx]
      split_ifs
      · exact this _
      · exact h0
    · rintro _ ⟨s, hs, rfl⟩
      rw [hL]
      intro l
      have := (mem_localization_standardLattice P _).1 hs
      rw [LinearMap.restrictScalars_apply, hc]
      split_ifs
      · exact this _
      · exact h0

end GlobalTheory.IndefiniteRowSideFullHecke.NormalFormInclusion
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def nfGen (q n c : ℕ) (e : Fin c → ℤ) (z : Sp E n) (i : Fin c) : Sp E (n + c) :=
  ((q : E) ^ e i) • (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0)

def nfLat (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ) (e : Fin c → ℤ) (z : Sp E n) : Set (Sp E (n + c)) :=
  {y | ∃ l ∈ stdAt E n P, ∃ s : Fin c → E, (∀ i, IntAt P (s i)) ∧
    y = Loc.inX E n c l + ∑ i, s i • nfGen (qOf P) n c e z i}

end Lattice

variable {X : Fields} {Pr : Primes X} {R : Ranks}

variable (Pr) in

def NF (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  ∃ (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)),
    (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧
    z ∈ stdAt X.E (R.N j) P ∧
    h '' (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = nfLat P (R.N j) (cOf R j) e z

variable (Pr) in

def Sandwich (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, ∃ y ∈ lamYat (Pr := Pr) (R := R) j P, h y = x) ∧
    ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P

variable (Pr R) in

def InclAt : Prop :=
  ∀ (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h k : AutY X R j, NF Pr j P h →
    k ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) → Sandwich Pr j P (h * k)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

def RepAt : Prop :=
  ∀ cst : LocCst X (rowSG Pr sel mu), cst.Ok →
  ∀ i : ℕ, i + 1 ≤ R.m - 2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
  ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), NF Pr i P.1 hal →
    (∀ x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1,
      ((qOf P.1 : X.E) ^ cst.D P) • h x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1) →
    FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h →
    ∃ h' : AutY X R (i + 1), SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' ∧ NF Pr (i + 1) P.1 h'

def IdxNF (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m - 2 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → NF Pr j P.1 (L.h j b P)

def ChoiceAt : Prop :=
  ∀ (cst : LocCst X (rowSG Pr sel mu)) (G : ChGlob X R.m) (m2 : ℕ) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))),
    L.Ok Ch sel mu cst G m2 →
    ∃ (A' B' : ℕ) (L' : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (e : ∀ j, L.β j ≃ L'.β j),
      cst.A ≤ A' ∧ cst.B ≤ B' ∧
      L'.Ok Ch sel mu { cst with A := A', B := B' } G m2 ∧
      IdxNF sel mu L' ∧
      (∀ j (b : L.β j) (P : rowSG Pr sel mu), SameDC (Pr := Pr) cst.sharp j P.1 (L.h j b P) (L'.h j (e j b) P)) ∧
      (∀ j (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L'.h j (e j b) P = L.h j b P) ∧
      (∀ j (b : L.β j), L'.levG j (e j b) = L.levG j b)

def NormalForm : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S),
    Module.finrank X.F X.E = 2 → IsSel X sel →
    InclAt Pr R ∧ RepAt Ch sel mu ∧ ChoiceAt Ch sel mu

theorem mem_lamYat {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (y : Sp X.E (R.N j + cOf R j)) :
    y ∈ lamYat (Pr := Pr) (R := R) j P ↔ ∀ l, IntAt P (y l) := by
  unfold lamYat LocE.lamY LocE.sclLat stdAt
  rw [if_neg hP, Submodule.mem_comap, mem_localization_standardLattice]
  simp [LocE.scE]

theorem nf_one (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) : NF (R := R) Pr j P 1 := by
  refine ⟨0, 0, fun i => ⟨by simp, le_rfl⟩, zero_mem _, ?_⟩
  have key : ∀ (l : Sp X.E (R.N j)) (s : Fin (cOf R j) → X.E) (p : Fin (R.N j + cOf R j)),
      (Loc.inX X.E (R.N j) (cOf R j) l + ∑ i, s i • nfGen (qOf P) (R.N j) (cOf R j) 0 0 i :
        Sp X.E (R.N j + cOf R j)) p =
        Fin.addCases (motive := fun _ => X.E) l s p := by
    intro l s p
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · have : ∀ i : Fin (cOf R j), ¬ (a.1 = R.N j + i.1) := fun i => by omega
      simp [Loc.inX, nfGen, Loc.eN, Finset.sum_apply, this]
    · simp [Loc.inX, nfGen, Loc.eN, Finset.sum_apply, Fin.val_inj]
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, mem_lamYat hP, nfLat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun a => x (Fin.castAdd _ a), (mem_localization_standardLattice _ _).2 fun a => hx _, fun b => x (Fin.natAdd _ b),
      fun b => hx _, ?_⟩
    funext p
    rw [key]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p <;> simp
  · rintro ⟨l, hl, s, hs, rfl⟩
    refine ⟨_, fun p => ?_, rfl⟩
    have hk := key l s p
    rw [Pi.add_apply] at hk
    rw [hk]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · simpa using (mem_localization_standardLattice _ _).1 hl a
    · simpa using hs b

end GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance

open Formalism.L2.Col

section Defs

variable {E : Type} [Field E] [NumberField E]

theorem intAt_zero (P : HeightOneSpectrum (𝓞 E)) : IntAt P (0 : E) :=
  ⟨0, 1, one_notMem P, by simp⟩

theorem intAt_add {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨s' * r + s * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
  ring

theorem intAt_mul {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']
  ring

theorem intAt_neg {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  exact ⟨-r, s, hs, by rw [map_neg, ← h]; ring⟩

theorem intAt_algebraMap (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E r) :=
  ⟨r, 1, one_notMem P, by simp⟩

def DegOneUnram (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  (qOf P).Prime ∧ ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2

def IsLatAt (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (abelian₂ : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  (∀ u : E, IntAt P u → ∀ v ∈ abelian₂, u • v ∈ abelian₂) ∧
    ∃ m : ℕ, (∀ v : Fin N → E, (∀ l, IntAt P (v l)) → ((qOf P : E) ^ m) • v ∈ abelian₂) ∧
      ∀ v ∈ abelian₂, ∀ l, IntAt P ((qOf P : E) ^ m * v l)

def adaptedVector (E : Type) [Field E] (n c i : ℕ) : Fin (n + c) → E := Loc.eN E (n + c) (n + (i - 1))

def unfoldedCoordinate {n c : ℕ} (i : ℕ) (v : Fin (n + c) → E) : E := Loc.atN v (n + (i - 1))

def srcGen (P : HeightOneSpectrum (𝓞 E)) (n' c' : ℕ) (e' : ℕ → ℤ) (z' : Fin n' → E) (i : ℕ) : Fin (n' + c') → E :=
  ((qOf P : E) ^ e' i) • (if i = 1 then adaptedVector E n' c' 1 + Loc.inX E n' c' z' else adaptedVector E n' c' i)

def srcLat (P : HeightOneSpectrum (𝓞 E)) {n' : ℕ} (c' : ℕ) (L' : Submodule (𝓞 E) (Fin n' → E)) (e' : ℕ → ℤ) (z' : Fin n' → E) :
    Submodule (𝓞 E) (Fin (n' + c') → E) where
  carrier := {v | ∃ l ∈ L', ∃ u : ℕ → E, (∀ i, IntAt P (u i)) ∧
    v = Loc.inX E n' c' l + ∑ i ∈ Finset.Icc 1 c', u i • srcGen P n' c' e' z' i}
  add_mem' := by
    rintro _ _ ⟨l, hl, u, hu, rfl⟩ ⟨l', hl', u', hu', rfl⟩
    refine ⟨l + l', L'.add_mem hl hl', fun i => u i + u' i, fun i => intAt_add (hu i) (hu' i), ?_⟩
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    abel
  zero_mem' := ⟨0, L'.zero_mem, fun _ => 0, fun _ => intAt_zero P, by simp⟩
  smul_mem' := by
    rintro r _ ⟨l, hl, u, hu, rfl⟩
    refine ⟨r • l, L'.smul_mem r hl, fun i => algebraMap (𝓞 E) E r * u i,
      fun i => intAt_mul (intAt_algebraMap P r) (hu i), ?_⟩
    rw [← algebraMap_smul E r, ← algebraMap_smul E r l, smul_add, map_smul, Finset.smul_sum]
    simp only [mul_smul]

def CondOOn {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (M : AddSubgroup E) : Prop :=
  (∀ a : E, IntAt P ((qOf P : E) * a) → a ∈ M) ∧ (∀ a ∈ M, ∀ b ∈ M, psi (a + b) = psi a * psi b) ∧
    (∀ a : E, IntAt P a → psi a = 1) ∧ psi ((qOf P : E)⁻¹) ≠ 1

def depthSub (P : HeightOneSpectrum (𝓞 E)) (D : ℕ) : AddSubgroup E where
  carrier := {a | IntAt P ((qOf P : E) ^ D * a)}
  add_mem' := fun {a b} ha hb => by
    show IntAt P _
    rw [mul_add]
    exact intAt_add ha hb
  zero_mem' := by
    show IntAt P _
    rw [mul_zero]
    exact intAt_zero P
  neg_mem' := fun {a} ha => by
    show IntAt P _
    rw [mul_neg]
    exact intAt_neg ha

def SuppOn {K : Type} [Field K] {a b : ℕ} (Lam' : Submodule (𝓞 E) (Fin a → E)) (abelian₂ : Submodule (𝓞 E) (Fin b → E))
    (Psi : Loc.SF E K a b) : Prop :=
  ∀ x, Psi x ≠ 0 → ∀ v ∈ Lam', x v ∈ abelian₂

def InvUnder {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (Lam' : Submodule (𝓞 E) (Fin a → E))
    (abelian₂ : Submodule (𝓞 E) (Fin b → E)) (Psi : Loc.SF E K a b) : Prop :=
  ∀ x y : (Fin a → E) →ₗ[E] (Fin b → E), (∀ v ∈ Lam', y v ∈ abelian₂) → Psi (x + (qOf P : E) • y) = Psi x

def unfoldAB {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (A B : ℕ) {n' c' n c : ℕ}
    (Psi : Loc.SF E K (n' + c') (n + c)) : Loc.SF E K n' n :=
  Loc.E1 psi (LocE.valsQ E (qOf P) A B) (((qOf P : K) ^ B)⁻¹) Psi

def Bounds (P : HeightOneSpectrum (𝓞 E)) {n' n c : ℕ} (e' : ℕ → ℤ) (z' : Fin n' → E) (abelian₂ : Submodule (𝓞 E) (Fin (n + c) → E))
    (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : Prop :=
  (∃ e : ℕ → ℤ, ∀ i, 1 ≤ i → i ≤ c →
    (∀ s : E, (∃ v ∈ abelian₂, v ∈ Loc.Ufl E n c i ∧ unfoldedCoordinate i v = s) ↔ ∃ u : E, IntAt P u ∧ s = (qOf P : E) ^ e i * u) ∧
      e' (i + 1) - 1 ≤ e i ∧ e i ≤ e' i) ∧
  ((qOf P : E) ^ e' 1) • (adaptedVector E n c 1 + Loc.inX E n c (xj z')) ∈ abelian₂

end Defs

def UnfoldedBounds : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)), DegOneUnram P →
  ∀ (psi : E → K) (M : AddSubgroup E), CondOOn P psi M →
  ∀ (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 →
  ∀ (L' : Submodule (𝓞 E) (Fin n' → E)), IsLatAt P L' →
  ∀ (e' : ℕ → ℤ) (z' : Fin n' → E) (abelian₂ : Submodule (𝓞 E) (Fin (n + c) → E)), IsLatAt P abelian₂ →
  ∀ (Psi : Loc.SF E K (n' + c') (n + c)), SuppOn (srcLat P c' L' e' z') abelian₂ Psi → InvUnder P (srcLat P c' L' e' z') abelian₂ Psi →
  ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E),
    (∀ t : Loc.FC n' c' n c → E, Psi (Loc.xx1 xj t) ≠ 0 → Loc.chArg (Loc.xx1 xj t) ∈ M) →
    unfoldAB P psi A B Psi xj ≠ 0 → Bounds P e' z' abelian₂ xj

example {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    IsLatAt P ({ carrier := {v | ∀ l, IntAt P (v l)}
                 add_mem' := fun ha hb l => intAt_add (ha l) (hb l)
                 zero_mem' := fun _ => intAt_zero P
                 smul_mem' := fun r v hv l => by
                   have := intAt_mul (intAt_algebraMap P r) (hv l)
                   simpa [Algebra.smul_def] using this } : Submodule (𝓞 E) (Fin N → E)) :=
  ⟨fun _ hu _ hv l => intAt_mul hu (hv l), 0, fun v hv l => by simpa using hv l, fun v hv l => by simpa using hv l⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance
end
end

