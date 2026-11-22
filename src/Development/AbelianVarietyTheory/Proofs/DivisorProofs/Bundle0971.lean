import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlPiEquivSymmContinuous
section
open Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

def matPiEquiv (S : Type) [CommRing S] (n k : ℕ) :
    Matrix (Fin n) (Fin n) (Fin k → S) ≃+* (Fin k → Matrix (Fin n) (Fin n) S) where
  toFun M i := (Pi.evalRingHom (fun _ : Fin k => S) i).mapMatrix M
  invFun N := Matrix.of fun a b i => N i a b
  left_inv M := by ext a b i; rfl
  right_inv N := by funext i; ext a b; rfl
  map_mul' M N := by funext i; exact map_mul ((Pi.evalRingHom (fun _ : Fin k => S) i).mapMatrix) M N
  map_add' M N := by funext i; exact map_add ((Pi.evalRingHom (fun _ : Fin k => S) i).mapMatrix) M N

theorem mem_range_map_subtype_iff {T : Type} [CommRing T] (n : ℕ) (A : Subring T) (g : GL (Fin n) T) :
    g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range ↔
      (∀ a b, (g : Matrix (Fin n) (Fin n) T) a b ∈ A) ∧
        (∀ a b, ((g⁻¹ : GL (Fin n) T) : Matrix (Fin n) (Fin n) T) a b ∈ A) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · change ((x : Matrix (Fin n) (Fin n) A) a b : T) ∈ A
      exact SetLike.coe_mem _
    · rw [← map_inv]
      change (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) a b : T) ∈ A
      exact SetLike.coe_mem _
  · rintro ⟨h1, h2⟩
    let P : Matrix (Fin n) (Fin n) A := Matrix.of fun a b => ⟨_, h1 a b⟩
    let Q : Matrix (Fin n) (Fin n) A := Matrix.of fun a b => ⟨_, h2 a b⟩
    have hP : P.map A.subtype = (g : Matrix (Fin n) (Fin n) T) := by ext a b; rfl
    have hQ : Q.map A.subtype = ((g⁻¹ : GL (Fin n) T) : Matrix (Fin n) (Fin n) T) := by ext a b; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) A => M.map A.subtype) := by
      intro M N h
      funext a b
      exact Subtype.ext (congrFun (congrFun h a) b)
    have hPQ : P * Q = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hP, hQ, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv)
    have hQP : Q * P = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hP, hQ, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul)
    refine ⟨⟨P, Q, hPQ, hQP⟩, ?_⟩
    ext a b
    rfl

def glPiEquiv {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S)) :
    GL (Fin n) R ≃* (Fin (d + 1) → GL (Fin n) S) :=
  (Units.mapEquiv (e.mapMatrix.trans (matPiEquiv S n (d + 1))).toMulEquiv).trans MulEquiv.piUnits

theorem glPiEquiv_val {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (g : GL (Fin n) R) (i : Fin (d + 1)) (a b : Fin n) :
    ((glPiEquiv d n e g i : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) a b = e ((g : Matrix (Fin n) (Fin n) R) a b) i :=
  rfl

theorem glPiEquiv_inv_val {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (g : GL (Fin n) R) (i : Fin (d + 1)) (a b : Fin n) :
    (((glPiEquiv d n e g i)⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) a b =
      e (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b) i :=
  rfl

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem glPiEquiv_mem_iff {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (A : Subring R) (B : Subring S) (hAB : ∀ x : R, x ∈ A ↔ ∀ i, e x i ∈ B) (g : GL (Fin n) R) :
    g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range ↔
      ∀ i, glPiEquiv d n e g i ∈ (GeneralLinearGroup.map (n := Fin n) B.subtype).range := by
  simp only [mem_range_map_subtype_iff, glPiEquiv_val, glPiEquiv_inv_val, hAB]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨fun a b => h1 a b i, fun a b => h2 a b i⟩
  · intro h
    exact ⟨fun a b i => (h i).1 a b, fun a b i => (h i).2 a b⟩

end GlobalTheory.LKRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFiniteOfHcFinite
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodFiniteDim

variable {D : D7}

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen (((Kg D.sp.cm V.gram β T).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β T] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem levFn_eq_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {T : Finset (Pl D.host.E)}
    (hg : L.Pg ⊆ T) (hq : L.Q ⊆ T) {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ Kg D.sp.cm V.gram β T) :
    levFn β L x = 1 := by
  have h3 : ∀ PP ∈ T, redFn β PP x = 1 := by
    have h1 : x ∈ ⨅ PP ∈ T, princAt β PP := hx.2
    exact fun PP hP => (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  have h4 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [h3 PP.1 (hg PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h4, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [h3 PP (hq hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

theorem exists_open_subgroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ (levG V β L : Set (GA D V)) ∧ levChi V β L k = 1 := by
  classical
  refine ⟨_, isOpen_comap_Kg V β (L.Pg ∪ L.Q), fun k hk hf => ⟨⟨hf, ?_⟩, ?_⟩⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk
  · unfold levChi
    rw [levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk, Units.val_one]

theorem goodFinite_of_hcFinite' (D : D7)
    (h : ∀ θ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (M : GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading.ModelW D j) J χ, HCFinite θ M J χ) :
    GlobalTheory.HeckeOrthSum.GoodFinite D := by
  intro θ hθ pb Pg _ pl _ red ψ _ om _ Sb _ j h1 h2 hj M β _
  have := h θ j h1 h2 M _ _ hθ (exists_open_subgroup (D.sp.W j) β (GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading.levelDatumAtBasePrime (D.sp.W j) Pg ψ))
  exact Submodule.finiteDimensional_of_le (goodPart_le θ M _ _ _)

theorem goodFinite_of_hcFinite : ∀ D : Formalism.BasicNotions.D7,
    (∀ θ (V : Formalism.BasicNotions.TH.HSp D) S (M : Formalism.IndefR.Mult.DSModel V S) J χ, Formalism.IndefR.Mult.HCFinite θ M J χ) →
      GlobalTheory.HeckeOrthSum.GoodFinite D := by
  intro D h θ hθ pb Pg _ pl _ red ψ _ om _ Sb _ j _ _ hj M β _
  have := h θ _ _ M _ _ hθ (exists_open_subgroup (D.sp.W j) β (GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading.levelDatumAtBasePrime (D.sp.W j) Pg ψ))
  exact Submodule.finiteDimensional_of_le (goodPart_le θ M _ _ _)

end GlobalTheory.GoodFiniteDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramNegTransposeDiag
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT in
open scoped ComplexOrder in

theorem isCartanInv_cart_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hu
  have hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have hJ' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  have hG : gramAt D V τ * cart M τ = (M.fr τ)ᴴ * M.fr τ := by
    rw [← M.fr_gram τ]; unfold cart
    calc _ = (M.fr τ)ᴴ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : cart M τ * cart M τ = 1 := by
    unfold cart
    calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← M.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (cart M τ)ᴴ * gramAt D V τ = gramAt D V τ * cart M τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (M.fr_unit τ))

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT in

theorem onb_gram_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    (onb M τ)ᴴ * gramAt D V τ * onb M τ = Formalism.REAL.Jm (M.ε τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  rw [← M.fr_gram τ]; unfold onb
  calc _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem gram_neg_transpose_diag {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ (-Gᵀ) x c c = -(xᴴ * G.map τ * x) c c := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.neg_apply,
    Matrix.transpose_apply, map_neg, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [RCLike.star_def]
  ring

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT in

theorem cart_mul_baseFrame : ∀ (D : D7) (W : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel W S) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ), Formalism.IndefR.FWT.IsModelBaseFrameFamily M rfl x₀ → ∀ ρ, IsCartanInv (gramAt D W ρ) (Formalism.IndefR.Links.cart M ρ) ∧ ∀ X : Data D.host.E W.rank, ModelW W rfl X → IsOrthogonalFrame X x₀ → tauE D ρ ∈ X.Ψ → Formalism.IndefR.Links.cart M ρ * x₀ (tauE D ρ) = -(x₀ (tauE D ρ) * sgnM X) := by
  intro D W S M x₀ hx ρ
  refine ⟨isCartanInv_cart_model M ρ, fun X hW hO hρ => ?_⟩
  have e : x₀ (tauE D ρ) = x0Mat M ρ := hx ρ
  have hG : X.Gm = -(W.gram)ᵀ := hW.1
  have hs : ∀ c : Fin W.rank, ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (c : ℕ) : ℝ) : ℂ) =
      -(if M.ε ρ (arr (nNeg (M.ε ρ)) c) then 1 else -1) := by
    intro c
    have h1 := congrFun (congrFun (hO _ hρ) c) c
    rw [hG, gram_neg_transpose_diag, Matrix.diagonal_apply_eq, e] at h1
    have h2 := congrFun (congrFun (onb_gram_model M ρ) (arr (nNeg (M.ε ρ)) c)) (arr (nNeg (M.ε ρ)) c)
    rw [Formalism.REAL.Jm, Matrix.diagonal_apply_eq] at h2
    rw [← h1, ← h2]
    rfl
  rw [e, cart, Formalism.REAL.Jm, torus_x0Mat]
  ext a c
  simp only [sgnM, Matrix.neg_apply, mul_diagonal, hs]
  ring

end GlobalTheory.FrameEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapBridge

theorem heckeChoiceClauses_of_weakCharacterisation_at_face : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ R.toRealDat.tup_mu_off ∧ R.toRealDat.tup_mu_used := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hC hE
  have h := RealDat3.characterisation_of_weak hC hE
  exact ⟨⟨h.lev, h.grp, h.fam, h.models, h.chain, h.thP⟩, h.tup.mu_off, h.tup.mu_used⟩

end GlobalTheory.OneMapBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeTrans

section Abstract

variable {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem mulVec_mem (S : Subring R) (u : Matrix m m S) (x : m → R) (hx : ∀ i, x i ∈ S) (i : m) :
    (u.map S.subtype).mulVec x i ∈ S := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact S.sum_mem fun k _ => S.mul_mem (u i k).2 (hx k)

theorem frame_inv (S : Subring R) (β : GL n R) (β' : GL m R) (c : n ≃ m) (U : GL m R) (u u' : Matrix m m S)
    (hu : U.val = u.map S.subtype) (hu' : (U⁻¹).val = u'.map S.subtype) (j : Matrix m n R)
    (hj : j * β.val = (β' * U).val.submatrix id c) :
    (∃ j' : Matrix n m R, j * j' = 1 ∧ j' * j = 1) ∧
      ∀ x : n → R, (∀ i, (β⁻¹).val.mulVec x i ∈ S) ↔ ∀ i, (β'⁻¹).val.mulVec (j.mulVec x) i ∈ S := by
  have hj2 : j = (β' * U).val.submatrix id c * (β⁻¹).val := by
    rw [← hj, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨⟨β.val * ((β' * U)⁻¹).val.submatrix c id, ?_, ?_⟩, fun x => ?_⟩
  · rw [← Matrix.mul_assoc, hj, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_id_id]
  · have h1 : ((β' * U)⁻¹).val.submatrix c id * (β' * U).val.submatrix id c = 1 := by
      have := Matrix.submatrix_mul_equiv ((β' * U)⁻¹).val (β' * U).val c (Equiv.refl m) c
      rw [Units.inv_mul, Matrix.submatrix_one_equiv] at this
      exact this
    rw [hj2, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.submatrix _ _ _), h1, Matrix.one_mul, Units.mul_inv]
  · have h1 : j.mulVec x = (β' * U).val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [hj2, ← Matrix.mulVec_mulVec, Matrix.submatrix_mulVec_equiv]
      rfl
    have h2 : (β'⁻¹).val.mulVec (j.mulVec x) = U.val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [h1, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [h2]
    constructor
    · intro h i
      rw [hu]
      exact mulVec_mem S u _ (fun k => h _) i
    · intro h i
      have h3 := mulVec_mem S u' _ h (c i)
      rw [← hu', Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Function.comp_apply, Equiv.symm_apply_apply] at h3
      exact h3

variable {f : R} {J : Matrix m n R} {J' : Matrix n m R} {M : Matrix n n R} {M' : Matrix m m R}

omit [DecidableEq n] in
theorem conj_eq (h1 : J * J' = 1) (hc : M' * J = J * M) : M' = J * M * J' := by
  rw [← hc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conj_inv (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M * J' = J' * M' := by
  rw [conj_eq h1 hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem supp_conj (h1 : J * J' = 1) (hc : M' * J = J * M) (hs : f • (M - 1) = M - 1) : f • (M' - 1) = M' - 1 := by
  have hs2 : M' - 1 = J * (M - 1) * J' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, ← conj_eq h1 hc]
  rw [hs2, ← Matrix.smul_mul, ← Matrix.mul_smul, hs]

theorem det_conj (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M'.det = M.det := by
  rw [conj_eq h1 hc]
  exact Matrix.det_conj_of_mul_eq_one h1 h2

variable {L : AddSubgroup (n → R)} {L' : AddSubgroup (m → R)}

omit [DecidableEq n] in
theorem lat_inv (h1 : J * J' = 1) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L') (y : m → R) :
    f • y ∈ L' ↔ f • J'.mulVec y ∈ L := by
  rw [hL, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

omit [DecidableEq n] in
theorem stab_conj (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc' : ∀ y ∈ L', f • y ∈ L') (ha : ∀ y ∈ L, f • M.mulVec y ∈ L) : ∀ y ∈ L', f • M'.mulVec y ∈ L' := by
  intro y hy
  have h3 := ha _ ((lat_inv h1 hL y).1 (loc' y hy))
  rw [hL, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← conj_eq h1 hc] at h3
  exact h3

omit [DecidableEq n] in
theorem cont_conj {p : R} (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc : ∀ y ∈ L, f • y ∈ L) (loc' : ∀ y ∈ L', f • y ∈ L') (hb : ∀ y ∈ L, ∃ z ∈ L, f • p • y = f • M.mulVec z) :
    ∀ y ∈ L', ∃ z ∈ L', f • p • y = f • M'.mulVec z := by
  intro y hy
  obtain ⟨z, hz, h3⟩ := hb _ ((lat_inv h1 hL y).1 (loc' y hy))
  refine ⟨f • J.mulVec z, (hL z).1 (loc z hz), ?_⟩
  have h4 := congrArg J.mulVec h3
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1,
    Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hc, smul_comm p, smul_smul, hf] at h4
  rw [h4, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec]

variable {R' : Type} [CommRing R']

omit [Fintype n] in
theorem supp_map_iff (φ : R' →+* R) (g : R') (A : Matrix n n R') :
    φ g • (A.map φ - 1) = A.map φ - 1 ↔ ∀ i j, φ (g * (A - 1) i j) = φ ((A - 1) i j) := by
  have h : ∀ i j, φ ((A - 1) i j) = (A.map φ - 1) i j := by
    intro i j
    rw [← Matrix.map_one φ φ.map_zero φ.map_one]
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub]
  simp only [map_mul, h]
  rw [← Matrix.ext_iff]
  rfl

omit [DecidableEq m] in
theorem map_mul_one (φ : R' →+* R) {A : Matrix n m R'} {B : Matrix m n R'} (h : A * B = 1) : A.map φ * B.map φ = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ φ.map_zero φ.map_one]

omit [DecidableEq m] [DecidableEq n] in
theorem map_conj (φ : R' →+* R) {A : Matrix m m R'} {B : Matrix m n R'} {C : Matrix n n R'} (h : A * B = B * C) :
    A.map φ * B.map φ = B.map φ * C.map φ := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

omit [DecidableEq m] [DecidableEq n] [Fintype m] in
theorem mulVec_map_inv (φ : R' →+* R) (ψ : R →+* R') (h : ∀ x, ψ (φ x) = x) (j : Matrix m n R') (y : n → R) :
    (j.mulVec fun a => ψ (f * y a)) = fun a => ψ (f * (j.map φ).mulVec y a) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, h]
  exact Finset.sum_congr rfl fun b _ => mul_left_comm _ _ _

theorem map_mul_det (φ : R' →+* R) (e : R') (A : Matrix m m R') (B : Matrix n n R') (h : (A.map φ).det = (B.map φ).det) :
    φ (e * A.det) = φ (e * B.det) := by
  rw [map_mul, map_mul, RingHom.map_det, RingHom.map_det]
  exact congrArg (φ e * ·) h

end Abstract

variable {D : D7}

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (mt V g).map (finPart D) := rfl

theorem inf_eq {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) : (mt V g).map (infPart D) = 1 :=
  congrArg Units.val (MonoidHom.mem_ker.1 hg)

theorem idem_det {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {m n : ℕ} (A : Matrix (Fin m) (Fin m) (Formalism.L2.Theta.AE D))
    (B : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)) (h : (A.map (finPart D)).det = (B.map (finPart D)).det) :
    e * A.det = e * B.det := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ (map_mul_det (finPart D) e A B h)
  simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]

theorem suppAt_iff (e : Formalism.L2.Theta.AE D) {V : HSp D} {α : GA D V} (hα : α ∈ GfC V) :
    SuppAt e V α ↔ finPart D (e + cA D e) • (finMat D.sp.cm.sig V.gram α - 1) = finMat D.sp.cm.sig V.gram α - 1 := by
  rw [finMat_eq, supp_map_iff]
  refine ⟨fun hs i j => congrArg (finPart D) (hs i j), fun hs i j => ?_⟩
  have hs4 := (supp_map_iff (infPart D) (e + cA D e) (mt V α)).1 (by rw [inf_eq hα, sub_self, smul_zero])
  exact GlobalTheory.SplitScalar.adele_ext (hs4 i j) (hs i j)

theorem transfer {V V' : HSp D} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e)
    (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (h1 : HMul.hMul J J' = 1) (h2 : HMul.hMul J' J = 1) {α : GA D V} {α' : GA D V'} (hα' : α' ∈ GfC V')
    (hc : HMul.hMul (finMat D.sp.cm.sig V'.gram α') J = HMul.hMul J (finMat D.sp.cm.sig V.gram α))
    (hL : ∀ y, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D e • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V')
    (loc : ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V)
    (loc' : ∀ y ∈ Formalism.L2.NTheta.LamHat V', finPart D e • y ∈ Formalism.L2.NTheta.LamHat V')
    {ϖ : D.host.E} {k : ℕ} (h : Formalism.L2.NTheta.IsHeckeElt V e ϖ k α) : Formalism.L2.NTheta.IsHeckeElt V' e ϖ k α' := by
  obtain ⟨hα, hs, ha, hb, u, u', hu, hu', huu, hd⟩ := h
  have hf : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he.1]
  refine ⟨hα', ?_, stab_conj hf h1 hc hL loc' ha, cont_conj hf h1 hc hL loc loc' hb, u, u', hu, hu', huu, ?_⟩
  · exact (suppAt_iff e hα').2 (supp_conj h1 hc ((suppAt_iff e hα).1 hs))
  · exact (idem_det he _ _ (det_conj h1 h2 hc)).trans hd

def unswap (D : D7) : EAf D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm.toAlgHom.toRingHom

theorem unswap_swap (x) : unswap D (swapAE D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm_apply_apply x

theorem swap_unswap (x) : swapAE D (unswap D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).apply_symm_apply x

theorem finE_unswap (V : HSp D) (g : GA D V) : (finE V g).val.map (unswap D) = finMat D.sp.cm.sig V.gram g := by
  ext i j
  exact unswap_swap _

theorem isHeckeAt_iff : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (β' : GL (Fin V'.rank) (EAf D)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N' : ℕ) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V') (PP : Pl D.host.E), IsFinIso V V' β β' Pg j Φ → IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ((N' : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ k (α : GfC V), IsHeckeAt V PP k α ↔ IsHeckeAt V' PP k (Φ α) := by
  intro D V V' β Λ N β' Λ' N' Pg j Φ PP hI hB hB' hN hN' k α
  obtain ⟨hr, u, hu, -⟩ := hI.frame
  obtain ⟨⟨j', h1, h2⟩, hlat⟩ := frame_inv (Formalism.L2.Herm.intAf D.host.F D.host.E) β β' (finCongr hr)
    (intGL D.host.F D.host.E V'.rank u) u.val (u⁻¹).val rfl rfl j hu
  have h1' := map_mul_one (unswap D) h1
  have h2' := map_mul_one (unswap D) h2
  have hc := map_conj (unswap D) (hI.conj α)
  rw [finE_unswap, finE_unswap] at hc
  have hc' := conj_inv h1' h2' hc
  have hL : ∀ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e PP → ∀ y, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V ↔
      finPart D e • (j.map (unswap D)).mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
    intro e he y
    refine ((GlobalTheory.T.idempotent_preserves_lattice_hat V β Λ N PP e hB hN he y).2.trans (hlat _)).trans
      (Iff.trans ?_ (GlobalTheory.T.idempotent_preserves_lattice_hat V' β' Λ' N' PP e hB' hN' he _).2.symm)
    rw [mulVec_map_inv (unswap D) (swapAE D) swap_unswap]
  constructor
  · rintro ⟨e, ϖ, he, hϖ, hϖ2, h⟩
    exact ⟨e, ϖ, he, hϖ, hϖ2, transfer he.1 _ _ h1' h2' (Φ α).2 hc (hL e he)
      (fun y => (GlobalTheory.T.idempotent_preserves_lattice_hat V β Λ N PP e hB hN he y).1) (fun y => (GlobalTheory.T.idempotent_preserves_lattice_hat V' β' Λ' N' PP e hB' hN' he y).1) h⟩
  · rintro ⟨e, ϖ, he, hϖ, hϖ2, h⟩
    exact ⟨e, ϖ, he, hϖ, hϖ2, transfer he.1 _ _ h2' h1' α.2 hc' (lat_inv h1' (hL e he))
      (fun y => (GlobalTheory.T.idempotent_preserves_lattice_hat V' β' Λ' N' PP e hB' hN' he y).1) (fun y => (GlobalTheory.T.idempotent_preserves_lattice_hat V β Λ N PP e hB hN he y).1) h⟩

end GlobalTheory.HeckeTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixesComplexFibrePureEndomorphismTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixes_complex_fibre_pure_endomorphism_torsion : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (N : IntermediateField ℚ ℂ) [NumberField N] (P : Out.PolAV (Sp (𝓞 N))) (W : P.A ⟶ P.A) [IsMonHom W] (r s : 𝓞 N), IsPureBC P.A W r s → ∀ q : ℕ, q.Prime → ∀ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → r - s ∉ 𝔮 → ∀ τ : ℂ ≃+* ℂ, (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → ∀ (A : Over (Sp ℂ)) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ → ∃ io : A.left ⟶ A.left, IsGrpPullback A A (spMap (τ : ℂ →+* ℂ)) io ∧ ∀ n : ℕ, ¬ q ∣ n → ∀ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ P.A, y ^ n = 1 → ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → x ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left → x ≫ io = spMap (τ : ℂ →+* ℂ) ≫ x := by
  first | exact @GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | exact GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | (intros; apply GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersActIntegralChartEigenDirectionsStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integers_act_integralChart_eigenDirections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), ∀ a : 𝓞 E, IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧ ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  first | exact @GlobalTheory.ChartAct.isIntHom_actX_and_eigen | exact GlobalTheory.ChartAct.isIntHom_actX_and_eigen | (intros; apply GlobalTheory.ChartAct.isIntHom_actX_and_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProofStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivationEqPartialLogCoords_proof : InvDerSt := by
  first | exact @GlobalTheory.InvDer.invDer | exact GlobalTheory.InvDer.invDer | (intros; apply GlobalTheory.InvDer.invDer <;> assumption)
end

