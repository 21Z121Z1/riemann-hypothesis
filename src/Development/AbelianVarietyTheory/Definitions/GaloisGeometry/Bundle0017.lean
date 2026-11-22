import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.ContraPair

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in

def barK (k : Kinf E a) : Kinf E a :=
  ⟨(star k.1)ᵀ, Matrix.mem_unitaryGroup_iff.2 (by
    have h : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
    have e : star ((star k.1)ᵀ) = k.1ᵀ := by
      ext i j : 1
      simp [Matrix.star_apply]
    have h' : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
    rw [e, ← Matrix.transpose_mul, h', Matrix.transpose_one])⟩

omit [IsTotallyComplex E] in

def invTOp : Op E a → Op E a
  | .fin k => .fin (invT a (Af E) k)
  | .cpt k => .cpt (barK k)
  | .lie X => .lie (toL (-(Matrix.of X)ᵀ))

def Paired (π π' : CuspSub E a) (s : Op E a → Op E a) : Prop :=
  ∃ B : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
    (∀ k φ ψ, B (π.op (.fin k) φ) (π'.op (s (.fin k)) ψ) = B φ ψ) ∧
    (∀ k φ ψ, B (π.op (.cpt k) φ) (π'.op (s (.cpt k)) ψ) = B φ ψ) ∧
    ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π'.op (s (.lie X)) ψ) = 0

end

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

def conjOp : Op L a → Op L a
  | .fin k => .fin (GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k)
  | .cpt k => .cpt (barK k)
  | .lie X => .lie fun i j => star (X i j)

def DualIsConj (π : CuspSub L a) : Prop := Paired π π conjOp

def DualIsConjBy (π : CuspSub L a) (ψ : HChar L) : Prop := Paired (π.twist ψ⁻¹) π conjOp

theorem dualIsConjBy_one (π : CuspSub L a) : DualIsConjBy π 1 ↔ DualIsConj π := by
  rw [DualIsConjBy, inv_one, CuspSub.twist_one, DualIsConj]

structure PolarizedPair (π : CuspSub L a) (χ : HChar (maximalRealSubfield L)) : Prop where
  sign : ∀ v : InfinitePlace (maximalRealSubfield L), χ.locInf v (-1) = (-1) ^ a
  dual : DualIsConjBy π (GlobalTheory.GalOfCusp.compNorm L χ)

end GlobalTheory.ContraPair

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

structure InertJunk {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A3 : FamIn3 K G Pl0 I0 (List ℕ) T m) : Prop where
  R : ∀ t Q s, A3.heckeRI t (Q, s) = 0 ∨
    ∃ s', Formalism.L2.Col.InertTypeOk (A3.A.r + m * A3.A.t) s' ∧ A3.heckeRI t (Q, s) = A3.heckeRI t (Q, s')
  L : ∀ j t Q s, A3.heckeLI j t (Q, s) = 0 ∨
    ∃ s', Formalism.L2.Col.InertTypeOk (A3.A.r + A3.A.t) s' ∧ A3.heckeLI j t (Q, s) = A3.heckeLI j t (Q, s')

def GoodGeneric {K : Type} [Field K] (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ χ ∈ X, chiIdem χ * lvlIdem P ψ ≠ 0

def TrISepWith (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)
    (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) →
      ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure RowDict (R : RealDat3 D A3 Ks) (t : T) (pl : (A3.rowI t).OpIx → Pl D.host.E)
    (cX c0 : (A3.rowI t).OpIx → List ℤ →₀ ℂ) : Prop where
  good : ∀ i, Good R.toRealDat t (pl i)
  op : ∀ h, IsOpsX R.toRealDat t h → ∀ i x, R.jX t ((A3.rowI t).opAll i x) = h (pl i) (cX i) (R.jX t x)
  mat : ∀ i, MatchE R.toRealDat t (pl i) (cX i) (c0 i)

structure LiftDict (R : RealDat3 D A3 Ks) (j : Fin D.R.m) (t : T) (pl : (A3.liftI j t).OpIx → Pl D.host.E)
    (cV cW : (A3.liftI j t).OpIx → List ℤ →₀ ℂ) : Prop where
  good : ∀ i, Good R.toRealDat t (pl i)
  op : ∀ h, IsOpsV R.toRealDat j t h → ∀ i x, R.jV j t ((A3.liftI j t).opAll i x) = h (pl i) (cV i) (R.jV j t x)
  mat : ∀ i, MatchW R.toRealDat j t (pl i) (cV i) (cW i)

def labW (j : Fin D.R.m) {I : Type} (pl : I → Pl D.host.E) (cW : I → List ℤ →₀ ℂ) (c : Pl D.host.E → List ℤ → ℂ) : I → ℂ :=
  fun i => evC (Wc D j) (pl i) (c (pl i)) (cW i)

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.LocGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}

variable (k N) in

abbrev AdGL : Type := GL (Fin N) k ⧸ Subgroup.center (GL (Fin N) k)

def CoeffLp (p : ℝ) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : Measure (AdGL k N)), μ.IsHaarMeasure →
    ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} →
      ∃ F : AdGL k N → ℝ, (∀ g : GL (Fin N) k, F (QuotientGroup.mk g) = ‖l (π g v)‖) ∧ MemLp F (ENNReal.ofReal p) μ

def IsSqIntCoeff (π : Representation ℂ (GL (Fin N) k) V) : Prop := CoeffLp 2 π

def IsTemperedCoeff (π : Representation ℂ (GL (Fin N) k) V) : Prop := ∀ ε : ℝ, 0 < ε → CoeffLp (2 + ε) π

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelCharactersEqReference
section
noncomputable section

namespace GlobalTheory.KerJ.CharModel

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

section General

variable {L : Type} [Field L] [NumberField L]

theorem prod_inf_mul_finPart (a : Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, infIdele L w (y w)) * finPartI L a = a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    { toFun := fun x => x.1 w, map_one' := rfl, map_mul' := fun _ _ => rfl }
  refine ⟨fun w => Units.map (p w) a, ?_⟩
  have h : ((∏ w, infIdele L w (Units.map (p w) a) : Ideles L) : AdeleRing (𝓞 L) L) = ((a : AdeleRing (𝓞 L) L).1, 1) := by
    rw [Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w ((a : AdeleRing (𝓞 L) L).1 w)) = ι (fun w => (a : AdeleRing (𝓞 L) L).1 w)
    rw [← map_prod]
    exact congrArg ι (Finset.univ_prod_mulSingle (fun w : InfinitePlace L => ((a : AdeleRing (𝓞 L) L).1 w : w.Completion)))
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem isFin_finPart (a : Ideles L) : IsFinIdele (finPartI L a) := fun _ => rfl

theorem isUnitary_of_orderDvd {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) : χ.IsUnitary := fun x => by
  have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
  have h2 : χ.1 x ^ n = 1 := by simpa using h1
  have h3 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3

end General

variable {D : D7} {C : CharFrame D} (Dt : DtTied D C) {nch : NChoice D} (Tp : TupTied D C nch)

theorem eDt_finPart (a : Ideles D.host.E) : Dt.eDt (finPartI D.host.E a) = Dt.eDt a := by
  obtain ⟨y, hy⟩ := prod_inf_mul_finPart a
  conv_rhs => rw [← hy]
  rw [map_mul, map_prod, Finset.prod_eq_one fun w _ => Dt.inf w (y w), one_mul]

theorem kernelCharacters_eq_reference : MtIs Dt Tp D.what₂.mu0 D.muTil := fun j a ha => by
  rw [Dt.muTil_eq j a ha, TupTied.tup, Tp.trueColumnChoices_heckeChar_reference_eq_one, mul_one]

theorem mtIs_unique {μ : D.what₂.Tup} {mt mt' : ℕ → D.Dt →* ℂˣ} (h : MtIs Dt Tp μ mt) (h' : MtIs Dt Tp μ mt')
    (j : Fin D.R.m) : mt (j.1 + 1) = mt' (j.1 + 1) := by
  refine MonoidHom.ext fun t => ?_
  obtain ⟨a, rfl⟩ := Dt.surj t
  rw [← eDt_finPart Dt a, h j _ (isFin_finPart a), h' j _ (isFin_finPart a)]

theorem exists_mtIs_iff (hm : 0 < D.R.m) (μ : D.what₂.Tup) :
    (∃ mt, MtIs Dt Tp μ mt) ↔ ∀ a, Dt.eDt a = 1 → (Tp.xi μ).1 (finPartI D.host.E a) = 1 := by
  constructor
  · rintro ⟨mt, h⟩ a ha
    have h1 := h ⟨0, hm⟩ _ (isFin_finPart a)
    have h2 := Dt.muTil_eq ⟨0, hm⟩ _ (isFin_finPart a)
    rw [eDt_finPart, ha, map_one] at h1 h2
    have h3 : (Tp.tup μ ⟨0, hm⟩).1 (finPartI D.host.E a) =
      (C.mu0 ⟨0, hm⟩).1 (finPartI D.host.E a) * (Tp.xi μ).1 (finPartI D.host.E a) := rfl
    rw [h3, ← h2, one_mul] at h1
    exact h1.symm
  · intro h
    let ξ : D.Dt →* ℂˣ := Dt.eDt.liftOfSurjective Dt.surj ⟨(Tp.xi μ).1.comp (finPartI D.host.E), fun a ha => h a ha⟩
    have hξ : ∀ a, ξ (Dt.eDt a) = (Tp.xi μ).1 (finPartI D.host.E a) := fun a =>
      MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
    refine ⟨fun j => D.muTil j * ξ, fun j a ha => ?_⟩
    rw [MonoidHom.mul_apply, Dt.muTil_eq j a ha, hξ, finPartI_eq_self ha]
    rfl

theorem not_mtIs (hm : 0 < D.R.m) {μ : D.what₂.Tup} {v : HeightOneSpectrum (𝓞 D.host.E)} {x : (v.adicCompletion D.host.E)ˣ}
    (hx : Dt.eDt (localIdele D.host.E v x) = 1) (hξ : (Tp.xi μ).loc v x ≠ 1) (mt : ℕ → D.Dt →* ℂˣ) : ¬ MtIs Dt Tp μ mt :=
  fun h => hξ (by
    have := (exists_mtIs_iff Dt Tp hm μ).1 ⟨mt, h⟩ _ hx
    rwa [finPartI_eq_self fun _ => rfl] at this)

theorem tup_eq_of_mtIs (hm : 0 < D.R.m) {μ μ' : D.what₂.Tup} {mt : ℕ → D.Dt →* ℂˣ} (h : MtIs Dt Tp μ mt)
    (h' : MtIs Dt Tp μ' mt) (a : Ideles D.host.E) (ha : IsFinIdele a) : (Tp.xi μ).1 a = (Tp.xi μ').1 a := by
  have h1 := (h ⟨0, hm⟩ a ha).symm.trans (h' ⟨0, hm⟩ a ha)
  exact mul_left_cancel (a := (C.mu0 ⟨0, hm⟩).1 a) h1

theorem mtType_of_mtIs {μ : D.what₂.Tup} {mt : ℕ → D.Dt →* ℂˣ} (h : MtIs Dt Tp μ mt) (u : D.what₂.Word) : MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  obtain ⟨n, hn, hord⟩ := Tp.xi_fin μ
  have hun : (Tp.tup μ ⟨i, hi⟩).IsUnitary := fun x => by
    have e : (Tp.tup μ ⟨i, hi⟩).1 x = (C.mu0 ⟨i, hi⟩).1 x * (Tp.xi μ).1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← eDt_finPart Dt a, h ⟨i, hi⟩ _ (isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← eDt_finPart Dt, h ⟨i, hi⟩ _ (isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag, TupTied.tup,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

include Dt Tp in

theorem mtType_muTil (u : D.what₂.Word) : MtType u D.muTil := mtType_of_mtIs Dt Tp (kernelCharacters_eq_reference Dt Tp) u

theorem mtType_word {u u' : D.what₂.Word} {mt : ℕ → D.Dt →* ℂˣ} (h : MtType u mt) : MtType u' mt := fun i hi => by
  obtain ⟨h1, e, he, h2⟩ := h i hi
  exact ⟨h1, e, fun τ => by rw [he τ, D.hcW_e, D.hcW_e], h2⟩

end GlobalTheory.KerJ.CharModel
end
end

