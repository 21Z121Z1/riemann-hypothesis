import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import ReciprocityTheory.BasicDefinitions.AdRep

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharUnramified
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1 H1)

section Triv

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O)
    (X : Type) [AddCommGroup X] [Module O X]

theorem twCoef_chi_one (g : G) (m : O ⊗[O] X) : twCoef (Γ.Wchi 1) Γ.χ₁ X g m = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [coefRep_tmul, twistRep_apply]
    congr 1
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • ((Γ.chi 1 g : O) • a) = a
    rw [GalData.chi_one, smul_smul]
    simp
  | add a b ha hb => rw [map_add, ha, hb]

def homModInertia (I : Subgroup G) : Set (H1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤) :=
  {c | ∃ z : ↥(Z1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤), Submodule.Quotient.mk z = c ∧
    ∀ g ∈ I, (z : G → O ⊗[O] X) g = 0}

theorem cocycle_add (z : ↥(Z1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤)) (g h : G) :
    (z : G → O ⊗[O] X) (g * h) = (z : G → O ⊗[O] X) g + (z : G → O ⊗[O] X) h := by
  rw [cocycle_mul z g h, twCoef_chi_one]

theorem homModInertia_eq_unr (I : Subgroup G) :
    homModInertia Γ X I = (unr (twCoef (Γ.Wchi 1) Γ.χ₁ X) I : Set _) := by
  ext c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  constructor
  · rintro ⟨z', hz, h⟩
    rw [← hz]
    exact (mk_mem_unr_of_trivial (twCoef_chi_one Γ X) I z').mpr h
  · intro h
    exact ⟨z, rfl, (mk_mem_unr_of_trivial (twCoef_chi_one Γ X) I z).mp h⟩

end Triv

def AdmChiOneUnramified {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n r : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : GalData ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)),
    Standing P K LL emb Γ.lam → IsTopGal (P.PD K) emb D Γ → D.T1 l → D.T2 l → D.T3 l →
    ∀ (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] [Finite X],
      adm (P.PD K) emb Γ D.t D.Ut (Γ.Wchi 1) X = homModInertia Γ X (Loc.IK K)

example {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O)
    (X : Type) [AddCommGroup X] [Module O X] (I : Subgroup G) : 0 ∈ homModInertia Γ X I :=
  ⟨0, rfl, fun _ _ => rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharacterHyp
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses

open Formalism.BasicNotions GlobalTheory.AdmLoc TensorProduct
open ReciprocityTheory.Def (H1)

variable {l : ℕ} [Fact l.Prime]

abbrev Gal (K LL : Loc.FinExt l) : Type 1 := GalData ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)

def Hyp (P : LocPrime l) (K LL : Loc.FinExt l) {n r : ℕ} (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : Gal K LL) : Prop :=
  Standing P K LL emb Γ.lam ∧ IsTopGal (P.PD K) emb D Γ ∧ D.T1 l ∧ D.T2 l ∧ D.T3 l

def admissibleClassesTwistedChar (P : LocPrime l) (K LL : Loc.FinExt l) {n r : ℕ} (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : Gal K LL) (c : ℕ) (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] :
    Set (H1 (twCoef (Γ.Wchi c) Γ.χ₁ X) ⊤) :=
  adm (P.PD K) emb Γ D.t D.Ut (Γ.Wchi c) X

def Stmt (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n r : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (D : TopData n r)
    (Γ : Gal K LL), Hyp P K LL emb D Γ →
    ∀ c : ℕ, 2 ≤ c → c ≤ D.t →
    ∀ (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] [Finite X],
      admissibleClassesTwistedChar P K LL emb D Γ c X = {0}

def RealisationStatementAll (L : LocTheory) : Prop := ∀ (l : ℕ) [Fact l.Prime], Stmt (L l)

theorem twCoef_Wchi {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O) (c : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] (g : G) (y : O ⊗[O] X) :
    twCoef (Γ.Wchi c) Γ.χ₁ X g y = (((Γ.ε g) ^ (-((c : ℤ) - 1)) : Oˣ) : O) • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, ha, hb, smul_add]
  | tmul a x =>
    rw [coefRep_tmul, twistRep_apply, smul_tmul']
    congr 1
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • (((Γ.chi c g : Oˣ) : O) • a) = _
    rw [smul_smul, ← Units.val_mul]
    congr 2
    simp [GalData.chi]

example : 2 ≤ exData.t ∧ exData.T1 41 ∧ exData.T2 41 ∧ exData.T3 41 := ⟨le_rfl, exData_T1_T2_T3_fortyOne⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineExtensions
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct

section Ext

variable {G : Type} [Group G] {LL : Type} [Field LL] {V W : Type} [AddCommGroup V] [Module LL V]
  [AddCommGroup W] [Module LL W]

def IsExt (ρ : Representation LL G V) (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL) : Prop :=
  Function.Injective i ∧ Function.Exact i p ∧ Function.Surjective p ∧
    (∀ g x, i (ρ g x) = ρ' g (i x)) ∧ ∀ g y, p (ρ' g y) = p y

def IsCocycleOf (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL) (c : G → V) : Prop :=
  ∃ e : W, p e = 1 ∧ ∀ g, ρ' g e = e + i (c g)

theorem IsExt.exists_cocycle {ρ : Representation LL G V} {ρ' : Representation LL G W} {i : V →ₗ[LL] W}
    {p : W →ₗ[LL] LL} (h : IsExt ρ ρ' i p) : ∃ c : G → V, IsCocycleOf ρ' i p c := by
  obtain ⟨-, hex, hs, -, hp⟩ := h
  obtain ⟨e, he⟩ := hs 1
  have : ∀ g, ∃ x, i x = ρ' g e - e := fun g => (hex _).mp (by rw [map_sub, hp, sub_self])
  choose c hc using this
  exact ⟨c, e, he, fun g => by rw [hc]; abel⟩

theorem IsExt.cocycle_mul {ρ : Representation LL G V} {ρ' : Representation LL G W} {i : V →ₗ[LL] W}
    {p : W →ₗ[LL] LL} (h : IsExt ρ ρ' i p) {c : G → V} (hc : IsCocycleOf ρ' i p c) (g k : G) :
    c (g * k) = c g + ρ g (c k) := by
  obtain ⟨e, -, he⟩ := hc
  apply h.1
  have h1 := he (g * k)
  rw [map_mul, Module.End.mul_apply, he k, map_add, he g, ← h.2.2.2.1, add_assoc] at h1
  rw [map_add]
  exact (add_left_cancel h1).symm

theorem IsExt.cocycle_sub_mem_coboundaries {ρ : Representation LL G V} {ρ' : Representation LL G W} {i : V →ₗ[LL] W}
    {p : W →ₗ[LL] LL} (h : IsExt ρ ρ' i p) {c c' : G → V} (hc : IsCocycleOf ρ' i p c)
    (hc' : IsCocycleOf ρ' i p c') : c - c' ∈ B1 ρ := by
  obtain ⟨e, h1, he⟩ := hc
  obtain ⟨e', h1', he'⟩ := hc'
  obtain ⟨x, hx⟩ := (h.2.1 (e - e')).mp (by rw [map_sub, h1, h1', sub_self])
  refine ⟨x, funext fun g => h.1 ?_⟩
  change i (ρ g x - x) = i (c g - c' g)
  rw [map_sub, map_sub, h.2.2.2.1, hx, map_sub, he, he']
  abel

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def extRep (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ)) : Representation LL G (V × LL) where
  toFun g := ((ρ g).coprod (LinearMap.toSpanSingleton LL V ((c : G → V) g))).prod (LinearMap.snd LL V LL)
  map_one' := by
    have h : (c : G → V) 1 = 0 := by simpa using c.2.2 1 1
    refine LinearMap.ext fun x => ?_
    simp [h]
  map_mul' g k := by
    refine LinearMap.ext fun x => ?_
    simp [c.2.2 g k]
    abel

theorem extRep_isExt (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ)) :
    IsExt ρ (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) ∧
      IsCocycleOf (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) (c : G → V) := by
  refine ⟨⟨LinearMap.inl_injective, Function.Exact.inl_snd, LinearMap.snd_surjective, fun g x => ?_,
    fun _ _ => rfl⟩, (0, 1), rfl, fun g => ?_⟩
  · simp [extRep]
  · simp [extRep]

end Ext

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

def H1fSubmodule {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) :
    Submodule LL (H1V ρ) :=
  ((finiteCocycles PD ρ).comap (continuousCocycles ρ).subtype).map (Submodule.mkQ _)

theorem mk_mem_H1fSub {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V)
    (c : ↥(continuousCocycles ρ)) : (Submodule.Quotient.mk c : H1V ρ) ∈ H1fSubmodule PD ρ ↔ (c : G → V) ∈ finiteCocycles PD ρ := by
  refine ⟨?_, fun h => ⟨c, h, rfl⟩⟩
  rintro ⟨c', ⟨-, x, hx⟩, h⟩
  obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).mp h
  refine ⟨c.2, x - b ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  have h1 : ρ g b - b = (c' : G → V) g - (c : G → V) g := congrFun hb g
  have h2 : (c : G → V) g = (c' : G → V) g - (ρ g b - b) := by rw [h1]; abel
  have h3 : actVB PD ρ g (b ⊗ₜ[Qp] (1 : B)) = ρ g b ⊗ₜ[Qp] (1 : B) := by simp [actVB]
  have h4 : (c' : G → V) g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x := hx g
  rw [h2, sub_tmul, sub_tmul, h4, map_sub, h3]
  abel

def ExtCrysAt [TopologicalSpace LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [IsModuleTopology LL V]
    (ρ : Representation LL G V), (∀ x, Continuous fun g => ρ g x) → IsCrys PD ρ →
  ∀ (W : Type) [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL), IsExt ρ ρ' i p →
  ∀ c : ↥(continuousCocycles ρ), IsCocycleOf ρ' i p (c : G → V) →
    (IsCrys PD ρ' ↔ (Submodule.Quotient.mk c : H1V ρ) ∈ H1fSubmodule PD ρ) ∧
    (IsCrys PD ρ' → ∀ (j : ZMod n) (U : Multiset ℤ),
      AdmLoc.HasJumps PD ρ (emb j) U → AdmLoc.HasJumps PD ρ' (emb j) (U + {0}))

end Per

def ExtCrys {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (lam : ↥(Loc.OL LL)),
    AdmLoc.Standing P K LL emb lam → ExtCrysAt (P.PD K) emb

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.InvariantsVanishing
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc
open ReciprocityTheory.Def (H2)

section Concl

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n r : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (D : TopData n r) (Γ : GalData G Qp LL O)

abbrev resK : Type := O ⧸ Ideal.span {Γ.lam}

abbrev resRep : Representation O G (TensorProduct O ↥Γ.T₀.L.T (resK Γ)) := twCoef Γ.W₀ Γ.χ₁ (resK Γ)

abbrev HH : Type := H1tw Γ.T₀.L Γ.χ₁

abbrev Hf : Submodule O (HH Γ) := latticeFiniteCohomology PD (twLattice Γ.T₀.L Γ.χ₁⁻¹)

def Concl [NeZero n] : Prop :=
  (resRep Γ).invariants = ⊥ ∧
  Subsingleton (H2 (resRep Γ) ⊤) ∧
  (Module.Free O (HH Γ) ∧ Module.Finite O (HH Γ) ∧ Module.finrank O (HH Γ) = r * n) ∧
  ((∃ C : Submodule O (HH Γ), IsCompl (Hf PD Γ) C) ∧ Module.finrank O ↥(Hf PD Γ) = D.dsum) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X],
    TensIso Γ.T₀.L Γ.χ₁ X ∧
      adm PD emb Γ D.t D.Ut Γ.W₀ X = (finiteSelmer PD Γ.T₀.L Γ.χ₁ X : Set _)

theorem invariants_eq_bot_iff :
    (resRep Γ).invariants = ⊥ ↔ ∀ x, (∀ g, resRep Γ g x = x) → x = 0 := by
  rw [Submodule.eq_bot_iff]
  exact Iff.rfl

example (x : resK Γ) : Γ.lam ^ 1 • x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [pow_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end Concl

def ErrorExponentStatement {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : FinExt l) (n r : ℕ) [NeZero n] (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    Standing P K LL emb Γ.lam → IsTopGal (P.PD K) emb D Γ →
    D.T1 l → D.T2 l → D.T3 l → Concl (P.PD K) emb D Γ

def Stmt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ErrorExponentStatement P

theorem letters_ne_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {n : ℕ}
    {emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)} {lam : ↥(OL LL)} (h : Standing P K LL emb lam) : n ≠ 0 := by
  have := K.2
  rw [h.2.2.1]
  exact Module.finrank_pos.ne'

example : exData.dsum = 2 := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing
end
end

