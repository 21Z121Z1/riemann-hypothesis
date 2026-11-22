import Mathlib
import Formalism.LocalToGlobal.Columns.AtTLemmas
import Formalism.LocalRingCardinality.DataArith
import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll

-- bundled from Formalism.LocalToGlobal.Columns.KernelArgumentHypothesisScalar
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

def lenO (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (Ow w) V) : ℕ∞ :=
  Module.length (Ow w) (A ⧸ B.comap A.subtype)

def lenOU (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (Ow w) V) : ℚ :=
  ((lenO w A B).toNat : ℚ) / (eW w : ℚ)

def mapO {V' : Type} [AddCommGroup V'] [Module K V'] (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[K] V') (A : Submodule (Ow w) V) :
    Submodule (Ow w) V' :=
  A.map (f.restrictScalars (Ow w))

def piO {ι : Type} (w : HeightOneSpectrum (𝓞 K)) (A : ι → Submodule (Ow w) V) : Submodule (Ow w) (ι → V) where
  carrier := {x | ∀ i, x i ∈ A i}
  add_mem' := fun hx hy i => (A i).add_mem (hx i) (hy i)
  zero_mem' := fun i => (A i).zero_mem
  smul_mem' := fun r _ hx i => (A i).smul_mem r (hx i)

def scalO (w : HeightOneSpectrum (𝓞 K)) (c : K) (A : Submodule (Ow w) V) : Submodule (Ow w) V :=
  mapO w (c • (LinearMap.id : V →ₗ[K] V)) A

end Gen

def sumShiftW {n : ℕ} (lam : DomWeight n) (b : ℤ) : ℤ := ∑ i, (lam.w i + b)

section LemB

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def TbSwC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (b : ℤ) : Submodule (Ow w) (ColV W Ch u j) :=
  scalO w ((Pr.T u : X.K) ^ b) (SwC W Ch u j w)

def TbSwNabC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (b : ℤ) : Submodule (Ow w) (ColV W Ch u j) :=
  scalO w ((Pr.T u : X.K) ^ b) (SwNabC W Ch u j w)

def LemBInclAt (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Prop :=
  TbSwC W Ch u j w b ≤ BvWC W Ch u j w P

def LemBIdxAt (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (τ : X.Tau) (b : ℤ) : Prop :=
  ∃ n : ℕ, lenO w (BvWC W Ch u 0 w P) (TbSwC W Ch u 0 w b) = n ∧
    (R.N 0 : ℤ) * (n : ℤ) = (eW w : ℤ) * (finrank X.K (MfV W Ch u) : ℤ) * sumShiftW (W.lamTrue u 0 τ) b

def LemBInclNabAt (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Prop :=
  TbSwNabC W Ch u j w b ≤ BvNabWC W Ch u j w P

def LemBIdxNabAt (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (τ : X.Tau) (b : ℤ) : Prop :=
  ∃ n : ℕ, lenO w (BvNabWC W Ch u 0 w P) (TbSwNabC W Ch u 0 w b) = n ∧
    (R.N 0 : ℤ) * (n : ℤ) = (eW w : ℤ) * (finrank X.K (MfV W Ch u) : ℤ) * sumShiftW (W.lamTrue u 0 τ) b

def LemmaBIncl : Prop :=
  X.Ok → Pr.Ok → ∀ (u : Pr.Word) (j : ℕ), j ≤ R.m → ∀ (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
    ∀ b : ℤ, -(W.lamTrue u j τ).detShift ≤ b → LemBInclAt W Ch u j w P b

def LemmaBIdx : Prop :=
  X.Ok → Pr.Ok → 2 * X.f * R.k < Pr.g 0 - 1 →
    ∀ (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
      ∀ b : ℤ, -(W.lamTrue u 0 τ).detShift ≤ b → LemBIdxAt W Ch u w P τ b

def LemmaBInclNab : Prop :=
  X.Ok → Pr.Ok → ∀ (u : Pr.Word) (j : ℕ), j ≤ R.m → ∀ (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
    ∀ b : ℤ, -(W.lamTrue u j τ).detShift ≤ b → LemBInclNabAt W Ch u j w P b

def LemmaBIdxNab : Prop :=
  X.Ok → Pr.Ok → 2 * X.f * R.k < Pr.g 0 - 1 →
    ∀ (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
      ∀ b : ℤ, -(W.lamTrue u 0 τ).detShift ≤ b → LemBIdxNabAt W Ch u w P τ b

def CoefBInclAt (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Prop :=
  ∀ d : ColDeco X Pr u (R.N j),
    scalO w ((Pr.T u : X.K) ^ b) (atW w (delAtr X.emb (W.lamTrue u j) d.1.Lsh)) ≤ atW w (BvLat W u j P d)

def CoefBIdxAt (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (τ : X.Tau) (b : ℤ) : Prop :=
  ∀ d : ColDeco X Pr u (R.N 0), ∃ n : ℕ,
    lenO w (atW w (BvLat W u 0 P d)) (scalO w ((Pr.T u : X.K) ^ b) (atW w (delAtr X.emb (W.lamTrue u 0) d.1.Lsh))) = n ∧
      (R.N 0 : ℤ) * (n : ℤ) = (eW w : ℤ) * (finrank X.K (VV X.K (W.lamTrue u 0)) : ℤ) * sumShiftW (W.lamTrue u 0 τ) b

def CoefLemmaBIncl : Prop :=
  X.Ok → Pr.Ok → ∀ (u : Pr.Word) (j : ℕ), j ≤ R.m → ∀ (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
    ∀ b : ℤ, -(W.lamTrue u j τ).detShift ≤ b → CoefBInclAt W u j w P b

def CoefLemmaBIdx : Prop :=
  X.Ok → Pr.Ok → ∀ (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
    ∀ b : ℤ, -(W.lamTrue u 0 τ).detShift ≤ b → CoefBIdxAt W u w P τ b

end LemB

section LemC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def UramOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColRamV W Ch u j) :=
  (UOp W Ch u j P).restrict fun _ h => UOp_mem_ColRamV W Ch u j P h

def DramOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColRamV W Ch u j) :=
  (DOp W Ch u j P).restrict fun _ h => DOp_mem_ColRamV W Ch u j P h

def TbUC (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Module.End X.K (ColV W Ch u j) :=
  ((Pr.T u : X.K) ^ b) • UOp W Ch u j P

def TbUR (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Module.End X.K (ColRamV W Ch u j) :=
  ((Pr.T u : X.K) ^ b) • UramOp W Ch u j P

def SramWC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (Ow w) (ColV W Ch u j) :=
  SwC W Ch u j w ⊓ (ColRamV W Ch u j).restrictScalars (Ow w)

def BramWC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) : Submodule (Ow w) (ColV W Ch u j) :=
  BvWC W Ch u j w P ⊓ (ColRamV W Ch u j).restrictScalars (Ow w)

def vdetTbU (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : ℚ :=
  (vAdd w (LinearMap.det (TbUR W Ch u j P b)) : ℚ) / (eW w : ℚ)

end LemC

section T5

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def bAtC [Nonempty X.Tau] (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) : ℤ := W.bTop u (tauOfC w P.1)

def TUprodR [Nonempty X.Tau] (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (MramV W Ch u) :=
  ((VVTc W u w).toList.map fun P => TbUR W Ch u 0 P (bAtC W u w P)).prod

def idxNlamC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : ℚ :=
  lidxUW w (MramL W Ch u) (NlamG W Ch u w)

def bndLemC (u : Pr.Word) (τ : X.Tau) : ℚ :=
  (finrank X.K (MfV W Ch u) : ℚ) * (sumShiftW (W.lamTrue u 0 τ) (W.bTop u τ) : ℚ) / (R.N 0 : ℚ) +
    ((R.N 0 : ℚ) - 1) * (finrank X.K (MramV W Ch u) : ℚ)

def idxBndC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : ℚ :=
  (R.m : ℚ) * ∑ τ ∈ topsP W u w, bndLemC W Ch u τ

def indexBoundPerDegree (u : Pr.Word) (Wt : X.Tau → ℕ) : ℝ :=
  (R.m : ℝ) * ∑ τ ∈ W.tops, ((W.aTop u τ : ℝ) / (R.k : ℝ) + 2 * (Wt τ : ℝ) + (R.k : ℝ) - 1)

def IsWtBound (u : Pr.Word) (Wt : X.Tau → ℕ) : Prop :=
  ∀ (τ : X.Tau) (i : Fin (R.N 0)), i.1 ≠ 0 → ((W.lamTrue u 0 τ).w i).natAbs ≤ Wt τ

def wtT {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : ℝ := 2 * lW w * (eW w : ℝ)

def priceIC (u : Pr.Word) : ℝ :=
  (1 / (finrank X.K (MramV W Ch u) : ℝ)) *
    ∑ᶠ w : {w : HeightOneSpectrum (𝓞 X.K) // prW w = Pr.T u}, wtT w.1 * ((idxNlamC W Ch u w.1 : ℚ) : ℝ)

def WeightHalf (Pr : Primes X) : Prop :=
  ∀ u : Pr.Word, ∑ᶠ w : {w : HeightOneSpectrum (𝓞 X.K) // seenC Pr u w}, wtT w.1 = Real.log (Pr.T u)

end T5

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

abbrev KerArg (u : Pr.Word) : Type := ∀ j : ℕ, ColV W Ch u j →ₗ[X.K] ColV W Ch u (j + 1)

variable {W Ch}

def colArg {u : Pr.Word} (kk : KerArg W Ch u) (i : ℕ) : MfV W Ch u →ₗ[X.K] ColV W Ch u i :=
  Formalism.HermitianLattices.LocalLatticeBases.chainK X.K (fun j => ColV W Ch u j) kk i

def KernelFourierIntegralBound {u : Pr.Word} (kk : KerArg W Ch u) (w : HeightOneSpectrum (𝓞 X.K)) (e1 : ℕ) : Prop :=
  ∀ j, j < R.m → ∀ s ∈ SwC W Ch u j w, ((Pr.T u : X.K) ^ e1) • UprodC W Ch u (j + 1) w (kk j s) ∈ SwC W Ch u (j + 1) w

def KernelArgumentHypothesisScalar {u : Pr.Word} (kk : KerArg W Ch u) (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) : Prop :=
  ∀ j, j < R.m → ∀ P, (UOp W Ch u (j + 1) P).comp (kk j) = ((c j P : X.Kˣ) : X.K) • (kk j).comp (UOp W Ch u j P)

def cProdC (W : Wts X Pr.Word R) {u : Pr.Word} (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) (w : HeightOneSpectrum (𝓞 X.K)) (j : ℕ) : X.Kˣ :=
  ∏ P ∈ VVTc W u w, c j P

def ScalarIntegralAtPlace (W : Wts X Pr.Word R) {u : Pr.Word} (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) (w : HeightOneSpectrum (𝓞 X.K)) (ga : ℕ → ℕ) : Prop :=
  ∀ j, j < R.m → ∃ r : Ow w, algebraMap (Ow w) X.K r = ((cProdC W c w j)⁻¹ : X.Kˣ) * (Pr.T u : X.K) ^ ga j

def eColC (R : Ranks) (e1 : ℕ) (ga : ℕ → ℕ) : ℕ := R.m * e1 + ∑ j ∈ Finset.range R.m, (R.m - j) * ga j

end Col

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RowFormsSum
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Abstract

variable {Γ D M : Type} [Group Γ] [MulAction Γ D] [AddCommGroup M] [Module ℚ M]

theorem rf_smul_one_coset (N : Subgroup Γ) (γ : Γ) : γ • ((1 : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N) ↔ γ ∈ N := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]

def rf_stabEquiv (N : Subgroup Γ) (r : D) :
    MulAction.stabilizer N r ≃ MulAction.stabilizer Γ ((r, ((1 : Γ) : Γ ⧸ N)) : D × Γ ⧸ N) where
  toFun n := ⟨(n.1 : Γ), Prod.ext n.2 ((rf_smul_one_coset N _).mpr n.1.2)⟩
  invFun γ := ⟨⟨γ.1, (rf_smul_one_coset N _).mp (congrArg Prod.snd γ.2)⟩, congrArg Prod.fst γ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rf_cs_subgroup (N : Subgroup Γ) [Finite (Γ ⧸ N)] (F : D → M) (hF : ∀ (γ : Γ) (d : D), F (γ • d) = F d)
    (hfin : ∀ d : D, Finite (MulAction.stabilizer Γ d)) (RΓ RN : Finset D)
    (hΓ : ∀ d : D, ∃! r, r ∈ RΓ ∧ r ∈ MulAction.orbit Γ d)
    (hN : ∀ d : D, ∃! r, r ∈ RN ∧ r ∈ MulAction.orbit N d) :
    ∑ r ∈ RN, ((Nat.card (MulAction.stabilizer N r) : ℚ))⁻¹ • F r =
      (Nat.card (Γ ⧸ N) : ℚ) • ∑ r ∈ RΓ, ((Nat.card (MulAction.stabilizer Γ r) : ℚ))⁻¹ • F r := by
  classical
  have := Fintype.ofFinite (Γ ⧸ N)
  have hinj : Function.Injective fun r : D => ((r, ((1 : Γ) : Γ ⧸ N)) : D × Γ ⧸ N) := fun a b h => congrArg Prod.fst h
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.fubini_over_orbits Γ (D × Γ ⧸ N) D M Prod.fst
    (fun y => Finset.univ.image fun a : Γ ⧸ N => (y, a)) (fun p => F p.1)
    (RN.image fun r : D => ((r, ((1 : Γ) : Γ ⧸ N)) : D × Γ ⧸ N)) RΓ (fun _ _ => rfl)
    (by
      intro p y
      rw [Finset.mem_image]
      constructor
      · rintro ⟨a, -, rfl⟩
        rfl
      · rintro rfl
        exact ⟨p.2, Finset.mem_univ _, rfl⟩)
    (fun γ p => hF γ p.1) hfin
    (by
      rintro ⟨d, a⟩
      induction a using QuotientGroup.induction_on with
      | H g =>
      obtain ⟨r0, ⟨hr0, n, hn⟩, huniq⟩ := hN (g⁻¹ • d)
      have hn' : (n : Γ) • g⁻¹ • d = r0 := hn
      refine ⟨(r0, ((1 : Γ) : Γ ⧸ N)), ⟨Finset.mem_image_of_mem _ hr0, (n : Γ) * g⁻¹, ?_⟩, ?_⟩
      · refine Prod.ext ?_ ?_
        · show ((n : Γ) * g⁻¹) • d = r0
          rw [mul_smul, hn']
        · show ((n : Γ) * g⁻¹) • ((g : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N)
          rw [MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel_right, eq_comm, QuotientGroup.eq, inv_one, one_mul]
          exact n.2
      · rintro p ⟨hp, γ, hγ⟩
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
        have h1 : γ • d = r := congrArg Prod.fst hγ
        have h2 : γ • ((g : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N) := congrArg Prod.snd hγ
        have h3 : γ * g ∈ N := by
          rw [MulAction.Quotient.smul_coe, smul_eq_mul, eq_comm, QuotientGroup.eq, inv_one, one_mul] at h2
          exact h2
        have h4 : r = r0 := huniq r ⟨hr, ⟨γ * g, h3⟩, by
          show (γ * g) • g⁻¹ • d = r
          rw [smul_smul, mul_inv_cancel_right, h1]⟩
        rw [h4])
    hΓ
  rw [Finset.sum_image (fun a _ b _ h => hinj h)] at key
  rw [Finset.smul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) (key.trans (Finset.sum_congr rfl fun y _ => ?_))
  · rw [Nat.card_congr (rf_stabEquiv N r)]
  · rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.snd h)]
    show _ • ∑ _a : Γ ⧸ N, F y = _
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul, smul_comm]

end Abstract

section TwoLevels

variable {X : Fields} {n r : ℕ} {ST SG SG0 : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) {ι : GLG X.E r SG0 →* GLG X.E n SG} {ΛP ΛK : LevFam X.E X.K n SG}
  {Λ0 : LevFam X.E X.K r SG0}

def rf_subN (ΛP ΛK : LevFam X.E X.K n SG) : Subgroup (FormG ΛP) where
  carrier := {g | (g.2.1 : GLG X.E n SG) ∈ ΛK.grp}
  one_mem' := ΛK.grp.one_mem
  mul_mem' := fun ha hb => ΛK.grp.mul_mem ha hb
  inv_mem' := fun ha => ΛK.grp.inv_mem ha

def rf_cosetEquiv (H : LevFam.Split ι ΛP ΛK Λ0) (hinj : ∀ a : ↥Λ0.grp, ι a.1 ∈ ΛK.grp → a = 1) :
    ↥Λ0.grp ≃ FormG ΛP ⧸ rf_subN ΛP ΛK :=
  Equiv.ofBijective (fun a => ((((1 : UF X.E n), (⟨ι a.1, (H.emb a).1⟩ : ↥ΛP.grp)) : FormG ΛP) : FormG ΛP ⧸ rf_subN ΛP ΛK)) (by
    constructor
    · intro a b hab
      have h1 := QuotientGroup.eq.mp hab
      have h2 : (ι a.1)⁻¹ * ι b.1 ∈ ΛK.grp := h1
      have h3 : ι ((a⁻¹ * b : ↥Λ0.grp) : GLG X.E r SG0) ∈ ΛK.grp := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        exact h2
      exact (inv_mul_eq_one.mp (hinj _ h3))
    · intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
      obtain ⟨a, k, e1, -⟩ := H.fac g.2
      refine ⟨a, QuotientGroup.eq.mpr ?_⟩
      show (ι a.1)⁻¹ * g.2.1 ∈ ΛK.grp
      rw [e1, inv_mul_cancel_left]
      exact k.2)

theorem rf_cs_split (H : LevFam.Split ι ΛP ΛK Λ0) (hinj : ∀ a : ↥Λ0.grp, ι a.1 ∈ ΛK.grp → a = 1)
    (hP : (formGSD C ΛP).Ok) (hK : (formGSD C ΛK).Ok) (sP : (formGSD C ΛP).Sec) (sK : (formGSD C ΛK).Sec)
    (F : DecoSet X.E n ST SG → X.K)
    (hF : ∀ (γ : UF X.E n) (h : ↥ΛP.grp) (d : DecoSet X.E n ST SG), F ((γ, (h.1 : GLG X.E n SG)) • d) = F d) :
    (formGSD C ΛK).csOf hK sK F = (Nat.card ↥Λ0.grp : X.K) * (formGSD C ΛP).csOf hP sP F := by
  classical
  let _ := hP.fintypeCl
  let _ := hK.fintypeCl
  have : Finite ↥Λ0.grp := inferInstance
  have : Finite (FormG ΛP ⧸ rf_subN ΛP ΛK) := Finite.of_equiv _ (rf_cosetEquiv H hinj)
  have hinjP : Function.Injective sP.rep := fun c c' hc => by rw [← sP.spec c, hc, sP.spec]
  have hinjK : Function.Injective sK.rep := fun c c' hc => by rw [← sK.spec c, hc, sK.spec]

  let up : FormG ΛK → ↥(rf_subN ΛP ΛK) := fun g => ⟨(g.1, ⟨g.2.1, (H.sub g.2).1⟩), g.2.2⟩
  let dn : ↥(rf_subN ΛP ΛK) → FormG ΛK := fun g => (g.1.1, ⟨g.1.2.1, g.2⟩)
  have hstab : ∀ d : DecoSet X.E n ST SG,
      MulAction.stabilizer (FormG ΛK) d ≃ MulAction.stabilizer ↥(rf_subN ΛP ΛK) d := fun d =>
    { toFun := fun g => ⟨up g.1, g.2⟩
      invFun := fun g => ⟨dn g.1, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have key := rf_cs_subgroup (Γ := FormG ΛP) (D := DecoSet X.E n ST SG) (M := X.K) (rf_subN ΛP ΛK) F
    (fun g d => hF g.1 g.2 d) hP.fin_stab (Finset.univ.image sP.rep) (Finset.univ.image sK.rep)
    (by
      intro a
      refine ⟨sP.rep ((formGSD C ΛP).cls a), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
      · exact ((formGSD C ΛP).cls_eq_iff _ _).mp (sP.spec _)
      · rintro r ⟨hr, hr2⟩
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
        have h1 : (formGSD C ΛP).cls (sP.rep c) = (formGSD C ΛP).cls a := ((formGSD C ΛP).cls_eq_iff _ _).mpr hr2
        rw [← h1, sP.spec])
    (by
      intro a
      refine ⟨sK.rep ((formGSD C ΛK).cls a), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
      · obtain ⟨g, hg⟩ := ((formGSD C ΛK).cls_eq_iff _ _).mp (sK.spec ((formGSD C ΛK).cls a))
        exact ⟨up g, hg⟩
      · rintro r ⟨hr, g, hg⟩
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
        have h1 : (formGSD C ΛK).cls (sK.rep c) = (formGSD C ΛK).cls a :=
          ((formGSD C ΛK).cls_eq_iff _ _).mpr ⟨dn g, hg⟩
        rw [← h1, sK.spec])
  rw [Finset.sum_image (fun c _ c' _ hc => hinjK hc), Finset.sum_image (fun c _ c' _ hc => hinjP hc)] at key
  unfold GSD.csOf
  rw [← Nat.card_congr (rf_cosetEquiv H hinj)] at key
  rw [Rat.smul_def, Rat.cast_natCast] at key
  refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (key.trans (congrArg _ (Finset.sum_congr rfl fun c _ => ?_)))
  · rw [(formGSD C ΛK).wt_eq, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, ← Nat.card_congr (hstab (sK.rep c)), smul_eq_mul]
  · rw [(formGSD C ΛP).wt_eq, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, smul_eq_mul]

theorem rf_ip_split (H : LevFam.Split ι ΛP ΛK Λ0) (hinj : ∀ a : ↥Λ0.grp, ι a.1 ∈ ΛK.grp → a = 1)
    (hP : (formGSD C ΛP).Ok) (hK : (formGSD C ΛK).Ok) (φ ψ : DecoSet X.E n ST SG → C.V)
    (hφ : φ ∈ (formGSD C ΛP).EqFun) (hψ : ψ ∈ (formGSD C ΛP).EqFun) :
    (formGSD C ΛP).ip hP φ ψ = ((Nat.card ↥Λ0.grp : X.K))⁻¹ * (formGSD C ΛK).ip hK φ ψ := by
  have h0 : (Nat.card ↥Λ0.grp : X.K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 := rf_cs_split C H hinj hP hK (formGSD C ΛP).outSec (formGSD C ΛK).outSec (fun d => C.pair (φ d) (ψ d))
    (fun γ h d => by
      have e1 := hφ ((γ, h) : FormG ΛP) d
      have e2 := hψ ((γ, h) : FormG ΛP) d
      show C.pair (φ ((γ, (h.1 : GLG X.E n SG)) • d)) (ψ ((γ, (h.1 : GLG X.E n SG)) • d)) = _
      have e1' : φ ((γ, (h.1 : GLG X.E n SG)) • d) = (formGSD C ΛP).ρ ((γ, h) : FormG ΛP) (φ d) := e1
      have e2' : ψ ((γ, (h.1 : GLG X.E n SG)) • d) = (formGSD C ΛP).ρ ((γ, h) : FormG ΛP) (ψ d) := e2
      rw [e1', e2']
      exact hP.inv _ _ _)
  show (formGSD C ΛP).csOf hP (formGSD C ΛP).outSec (fun d => C.pair (φ d) (ψ d)) =
    _ * (formGSD C ΛK).csOf hK (formGSD C ΛK).outSec (fun d => C.pair (φ d) (ψ d))
  rw [h1, inv_mul_cancel_left₀ h0]

end TwoLevels

section Rows

theorem rf_diagEmb_mem_HK {κ : Type} [CommRing κ] {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (g : GL (Fin r) κ)
    (hg : diagEmb κ h g ∈ HK n κ r bl) : g = 1 := by
  rw [HK_eq_HPar h bl, mem_HPar] at hg
  obtain ⟨hB, h0⟩ := hg
  have := Subgroup.mem_bot.mp h0
  rwa [firstBlock_diagEmb_eq] at this

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem rf_g0Hat_injX (a : G0 X.E Pr.vGs R.r) (ha : unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) a ∈ (rowTyKK Ch sel mu).grp) : a = 1 := by
  funext w
  have h1 : unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) a (inlSG w) ∈ (((rowTyK Ch).glue
      (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))) (inlSG w)).H :=
    (rowTyKK Ch sel mu).mem_at ⟨_, ha⟩ (inlSG w)
  rw [LevFam.glue_of_mem _ _ (inlSG w) w.2] at h1
  have h2 : unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) a (inlSG w) = diagEmb _ (r_le_X' R) (a w) := extGLG_of_mem _ (inlSG w) w.2
  have h3 : diagEmb _ (r_le_X' R) (a w) ∈ HK (R.N R.m - 1) (𝓞 X.E ⧸ w.1.asIdeal) R.r (List.replicate R.m R.t) := by
    rw [← h2]
    exact h1
  exact rf_diagEmb_mem_HK _ _ _ h3

theorem rf_g0Hat_injV (j : ℕ) (a : G0 X.E Pr.vGs R.r) (ha : unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) a ∈ (mtTyKK Ch sel mu j).grp) :
    a = 1 := by
  funext w
  have h1 : unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) a (inlSG w) ∈ (((mtTyK Ch j).glue
      (mtTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))) (inlSG w)).H :=
    (mtTyKK Ch sel mu j).mem_at ⟨_, ha⟩ (inlSG w)
  rw [LevFam.glue_of_mem _ _ (inlSG w) w.2] at h1
  have h2 : unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) a (inlSG w) = diagEmb _ (r_le_nV R) (a w) := extGLG_of_mem _ (inlSG w) w.2
  have h3 : diagEmb _ (r_le_nV R) (a w) ∈ HK R.nV (𝓞 X.E ⧸ w.1.asIdeal) R.r [R.t] := by
    rw [← h2]
    exact h1
  exact rf_diagEmb_mem_HK _ _ _ h3

theorem levelSumX (h : (mtildeGSD W Ch sel mu P).Ok) (h' : (mtildeKGSD W Ch sel mu).Ok)
    (φ ψ : DecoSet X.E (R.N R.m - 1) ∅ (rowSG Pr sel mu) → VV X.K W.sgTrue)
    (hφ : φ ∈ (mtildeGSD W Ch sel mu P).EqFun) (hψ : ψ ∈ (mtildeGSD W Ch sel mu P).EqFun) :
    (mtildeGSD W Ch sel mu P).ip h φ ψ = ((Nat.card P.grp : X.K))⁻¹ * (mtildeKGSD W Ch sel mu).ip h' φ ψ := by
  exact rf_ip_split (rowVal W (rowSG Pr sel mu)) (rowTy_split Ch sel mu P).inv
    (fun a ha => Subtype.ext (rf_g0Hat_injX Ch sel mu a.1 ha)) h h' φ ψ hφ hψ

theorem levelSumV (j : ℕ) (h : (mtGSD W Ch sel mu P j).Ok) (h' : (mtKGSD W Ch sel mu j).Ok)
    (φ ψ : DecoSet X.E R.nV ∅ (rowSG Pr sel mu) → VV X.K (W.lamV j))
    (hφ : φ ∈ (mtGSD W Ch sel mu P j).EqFun) (hψ : ψ ∈ (mtGSD W Ch sel mu P j).EqFun) :
    (mtGSD W Ch sel mu P j).ip h φ ψ = ((Nat.card P.grp : X.K))⁻¹ * (mtKGSD W Ch sel mu j).ip h' φ ψ := by
  exact rf_ip_split (mtVal W j (rowSG Pr sel mu)) (mtTy_split Ch sel mu P j).inv
    (fun a ha => Subtype.ext (rf_g0Hat_injV Ch sel mu j a.1 ha)) h h' φ ψ hφ hψ

theorem levelCsX (h : (mtildeGSD W Ch sel mu P).Ok) (h' : (mtildeKGSD W Ch sel mu).Ok)
    (F : DecoSet X.E (R.N R.m - 1) ∅ (rowSG Pr sel mu) → X.K)
    (hF : ∀ (g : (mtildeGSD W Ch sel mu P).G) (d : (mtildeGSD W Ch sel mu P).D), F (g • d) = F d) :
    (mtildeKGSD W Ch sel mu).csOf h' (mtildeKGSD W Ch sel mu).outSec F =
      (Nat.card P.grp : X.K) * (mtildeGSD W Ch sel mu P).csOf h (mtildeGSD W Ch sel mu P).outSec F := by
  exact rf_cs_split (rowVal W (rowSG Pr sel mu)) (rowTy_split Ch sel mu P).inv
    (fun a ha => Subtype.ext (rf_g0Hat_injX Ch sel mu a.1 ha)) h h' _ _ F
    (fun γ k d => hF (γ, k) d)

end Rows

end Formalism.L2.Col
end
end

